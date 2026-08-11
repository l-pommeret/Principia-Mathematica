#!/usr/bin/env python3
"""Fail-closed 1:1 remapping of Aristotle interface archives.

This tool is deliberately *not* a Lean compiler and never writes a canonical
edition source.  It makes an archive transplantable only as an interface-only
candidate after checking all of the following mechanically:

* the immutable archive digest and every Lean-member digest;
* byte-for-byte declaration signatures (modulo the enclosing namespace);
* a bijection from every archive declaration to a canonical declaration; and
* absence of placeholders, unsafe features, or an unmapped local declaration.

The resulting JSON is evidence for a later independent kernel check, never a
promotion or CI result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_AUDIT = ROOT / "reviews/Q228-Q244-aristotle-archive-audit.json"
SUPPORTED_BATCHES = ("Q228", "Q229", "Q230", "Q259", "Q296", "Q300")
STRICT_INSERTION_BATCHES = {"Q259", "Q300"}
RFL_ONLY_INSERTION_BATCHES = {"Q296"}
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "Classical": re.compile(r"\bClassical(?:\.|\b)"),
}
DECLARATION = re.compile(
    r"(?m)^[ \t]*(theorem|def|abbrev|axiom|opaque|inductive|structure|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
NAMESPACE = re.compile(r"(?m)^[ \t]*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
END = re.compile(r"(?m)^[ \t]*end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$")


class RemapError(ValueError):
    """A condition which makes an interface archive non-transplantable."""


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def safe_member_name(name: str) -> bool:
    path = PurePosixPath(name)
    return not path.is_absolute() and ".." not in path.parts and "\x00" not in name


def blank_comments(source: str) -> str:
    """Preserve offsets/newlines while blanking Lean line and block comments."""
    result = list(source)
    index = 0
    block_depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            block_depth += 1
            result[index:index + 2] = "  "
            index += 2
            continue
        if block_depth and source.startswith("-/", index):
            block_depth -= 1
            result[index:index + 2] = "  "
            index += 2
            continue
        if block_depth:
            if source[index] != "\n":
                result[index] = " "
            index += 1
            continue
        if source.startswith("--", index):
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            for cursor in range(index, end):
                result[cursor] = " "
            index = end
            continue
        index += 1
    if block_depth:
        raise RemapError("unterminated Lean block comment")
    return "".join(result)


def declaration_signature(source: str, start: int, limit: int) -> str:
    """Return the exact declaration header, excluding ``:=`` and its body."""
    segment = source[start:limit]
    body = blank_comments(segment)
    if body.lstrip().startswith(("axiom ", "opaque ")):
        newline = segment.find("\n")
        return (segment if newline < 0 else segment[:newline]).rstrip() + "\n"
    assignment = body.find(":=")
    where = re.search(r"(?m)^\s*where\s*$", body)
    cutoff = assignment if assignment >= 0 else (where.start() if where else len(segment))
    return segment[:cutoff].rstrip() + "\n"


def scan_declarations(source: str, path: str) -> list[dict[str, Any]]:
    """Extract global declarations and exact source headers without elaborating."""
    clean = blank_comments(source)
    events: list[tuple[int, str, Any]] = []
    events.extend((match.start(), "namespace", match) for match in NAMESPACE.finditer(clean))
    events.extend((match.start(), "end", match) for match in END.finditer(clean))
    events.extend((match.start(), "declaration", match) for match in DECLARATION.finditer(clean))
    events.sort(key=lambda item: item[0])
    namespaces: list[list[str]] = []
    declarations: list[dict[str, Any]] = []
    for position, kind, match in events:
        if kind == "namespace":
            namespaces.append(match.group(1).split("."))
        elif kind == "end":
            if namespaces:
                namespaces.pop()
        else:
            declarations.append({
                "path": path,
                "start": position,
                "kind": match.group(1),
                "name": match.group(2),
                "qualified": ".".join(
                    [part for frame in namespaces for part in frame] + match.group(2).split(".")
                ),
            })
    for index, declaration in enumerate(declarations):
        same_file = [candidate for candidate in declarations[index + 1:]
                     if candidate["path"] == declaration["path"]]
        limit = same_file[0]["start"] if same_file else len(source)
        declaration["signature"] = declaration_signature(source, declaration["start"], limit)
        declaration["signature_sha256"] = sha256_text(declaration["signature"])
        declaration["body"] = source[declaration["start"]:limit].rstrip() + "\n"
    return declarations


def signature_from_snippet(snippet: str) -> str:
    declarations = scan_declarations(snippet, "<signature>")
    if len(declarations) != 1:
        raise RemapError("a target signature must contain exactly one declaration")
    return declarations[0]["signature"]


def prompt_signatures(path: Path) -> list[dict[str, str]]:
    source = path.read_text(encoding="utf-8")
    fenced = re.findall(r"```lean\n(.*?)```", source, flags=re.DOTALL)
    result: list[dict[str, str]] = []
    for block in fenced:
        for declaration in scan_declarations(block, str(path)):
            if declaration["kind"] == "theorem":
                result.append({
                    "source": declaration["qualified"],
                    "signature": declaration["signature"],
                })
    return result


def expected_archive_hash(root: Path, batch: str) -> str | None:
    # Q300's terminal archive is deliberately retained only as negative
    # evidence.  Its immutable digest still belongs in the plan so a later
    # replacement cannot masquerade as this reviewed failure.
    if batch == "Q300":
        return "15b9639c4cbff8d2e2066999f33c0fd06b572cc84fdbaa0eac2f03ef269ba065"
    if batch == "Q259":
        return "71fca398baa073201f5975ff632c75de1d8659b504de0c858ae90c2b7d0e0b6e"
    if not ARCHIVE_AUDIT.is_file() or root != ROOT:
        audit_path = root / "reviews/Q228-Q244-aristotle-archive-audit.json"
    else:
        audit_path = ARCHIVE_AUDIT
    if not audit_path.is_file():
        return None
    payload = json.loads(audit_path.read_text(encoding="utf-8"))
    for record in payload.get("archives", []):
        if record.get("batch") == batch:
            return record.get("sha256")
    return None


def batch_plan(root: Path, batch: str) -> dict[str, Any]:
    """Return the source-to-canonical targets already audited for a batch."""
    if batch not in SUPPORTED_BATCHES:
        raise RemapError(f"unsupported batch {batch!r}")
    manifest = json.loads((root / "aristotle/manifests" / f"{batch}.json").read_text(
        encoding="utf-8"
    ))
    targets: list[dict[str, str]] = []
    if batch in {"Q228", "Q229", "Q230"}:
        declared = manifest["target_declarations"]
        signatures = manifest["interface_signature_targets"]
        for identifier in manifest["target_order"]:
            signature = signature_from_snippet(signatures[identifier])
            targets.append({
                "id": identifier,
                "source": declared[identifier],
                "canonical": declared[identifier],
                "signature": signature,
            })
    else:
        # Architecture targets have no canonical theorem body yet.  The
        # prompt is nevertheless the exact interface authority for the
        # source header, while metadata gives the intended edition locus.
        # Q296's signature is authoritative in its strict manifest, not in a
        # prose prompt copy.  This makes the recorded hash a direct manifest
        # derivative and avoids accepting a later prompt drift.
        if batch == "Q296":
            prompt_targets = [
                {
                    "source": manifest["target_declarations"][identifier],
                    "signature": signature_from_snippet(
                        manifest["interface_signature_targets"][identifier]
                    ),
                }
                for identifier in manifest["target_order"]
            ]
        else:
            prompt_targets = prompt_signatures(root / "aristotle" / f"{batch}.md")
        declared_targets = set(manifest.get("target_declarations", {}).values())
        if declared_targets:
            # The reviewed context may itself contain regression theorems.
            # They are scaffolding, never remap targets; retain only the exact
            # declarations named by the manifest's target order.
            prompt_targets = [
                target for target in prompt_targets
                if target["source"] in declared_targets
            ]
            if {target["source"] for target in prompt_targets} != declared_targets:
                raise RemapError(f"prompt/manifest target mismatch for {batch}")
        item_file = (
            root / "metadata/items/PM1-star-14-Q296.json"
            if batch == "Q296"
            else root / "metadata/items/PM1-star-9-Q259.json"
        )
        # Q300 is a prerequisite proof rather than a source-backfill batch,
        # so it deliberately has no separate item-registry file yet.
        item_payload = (
            json.loads(item_file.read_text(encoding="utf-8"))
            if batch in {"Q259", "Q296"}
            else []
        )
        items = item_payload.get("items", []) if isinstance(item_payload, dict) else item_payload
        if not isinstance(items, list):
            raise RemapError("Q259 item registry has no item list")
        canonical_by_short_name = {
            record["declaration"].rsplit(".", 1)[-1]: record["declaration"]
            for record in items
        }
        if batch == "Q300":
            # Q300 is intentionally routed to the prerequisite theorem
            # demanded by its Q301 sequential-remap gate, not to a fabricated
            # edition declaration.
            canonical_by_short_name["star_9_21"] = (
                "PM.Architecture.FirstOrderPrerequisites.star_9_21"
            )
        for target in prompt_targets:
            short_name = target["source"].rsplit(".", 1)[-1]
            canonical = canonical_by_short_name.get(short_name)
            if canonical is None:
                raise RemapError(f"no canonical target registered for {target['source']}")
            targets.append({
                "id": next((record["id"] for record in items
                            if record["declaration"].rsplit(".", 1)[-1] == short_name),
                          "PM1:✱9·21"),
                "source": target["source"],
                "canonical": canonical,
                "signature": target["signature"],
                # This theorem is the artifact to insert.  It is not a
                # pre-existing dependency, so its present absence cannot be
                # used to reject a body which otherwise remaps exactly.
                "insertion_target": batch in {"Q296", *STRICT_INSERTION_BATCHES},
            })
            if batch in RFL_ONLY_INSERTION_BATCHES:
                targets[-1]["body_policy"] = "rfl-only"
    for target in targets:
        target["signature_sha256"] = sha256_text(target["signature"])
    return {
        "kind": "pm-interface-kernel-remap-plan",
        "batch": batch,
        "archive_sha256": expected_archive_hash(root, batch),
        "targets": targets,
        "canonical_integration_forbidden": True,
        "requires_one_to_one_kernel_remap": True,
        "no_local_lean_or_ci_was_run": True,
    }


def find_canonical_declarations(root: Path, names: set[str]) -> dict[str, dict[str, Any]]:
    found: dict[str, dict[str, Any]] = {}
    for path in sorted((root / "Principia").rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        for declaration in scan_declarations(source, str(path.relative_to(root))):
            if declaration["qualified"] in names:
                if declaration["qualified"] in found:
                    raise RemapError(f"duplicate canonical declaration {declaration['qualified']}")
                found[declaration["qualified"]] = declaration
    return found


def load_mapping(path: Path | None) -> list[dict[str, str]]:
    if path is None:
        return []
    payload = json.loads(path.read_text(encoding="utf-8"))
    records = payload.get("declarations", payload)
    if not isinstance(records, list):
        raise RemapError("mapping must be a list or an object with declarations")
    clean: list[dict[str, str]] = []
    for record in records:
        if not isinstance(record, dict) or set(record) - {"source", "canonical"}:
            raise RemapError("each mapping must contain only source and canonical")
        if not all(isinstance(record.get(key), str) and record[key] for key in ("source", "canonical")):
            raise RemapError("each mapping needs non-empty source and canonical names")
        clean.append({"source": record["source"], "canonical": record["canonical"]})
    if len({record["source"] for record in clean}) != len(clean):
        raise RemapError("a local declaration has more than one mapping")
    if len({record["canonical"] for record in clean}) != len(clean):
        raise RemapError("mapping is not one-to-one: canonical declaration repeated")
    return clean


def archive_sources(path: Path) -> tuple[
        str, list[dict[str, Any]], list[dict[str, Any]], list[str], list[str]]:
    if not path.is_file():
        raise RemapError(f"archive not found: {path}")
    archive_digest = sha256_bytes(path.read_bytes())
    files: list[dict[str, Any]] = []
    declarations: list[dict[str, Any]] = []
    failures: list[str] = []
    imports: list[str] = []
    with tarfile.open(path, "r:*") as archive:
        for member in archive.getmembers():
            if not safe_member_name(member.name):
                raise RemapError(f"unsafe archive path {member.name!r}")
            if member.issym() or member.islnk():
                raise RemapError(f"archive link is not permitted: {member.name!r}")
            if not member.isfile() or not member.name.endswith(".lean"):
                continue
            extracted = archive.extractfile(member)
            if extracted is None:
                raise RemapError(f"cannot read Lean member {member.name!r}")
            raw = extracted.read()
            try:
                source = raw.decode("utf-8")
            except UnicodeDecodeError as error:
                raise RemapError(f"non-UTF-8 Lean member {member.name!r}") from error
            files.append({"path": member.name, "bytes": len(raw), "sha256": sha256_bytes(raw)})
            clean = blank_comments(source)
            for label, pattern in FORBIDDEN.items():
                if pattern.search(clean):
                    failures.append(f"{member.name}: forbidden {label}")
            imports.extend(
                f"{member.name}: {match.group(0).strip()}"
                for match in re.finditer(r"(?m)^\s*import\s+.+$", clean)
            )
            declarations.extend(scan_declarations(source, member.name))
    if not files:
        raise RemapError("archive contains no Lean source")
    return archive_digest, files, declarations, failures, imports


def is_rfl_only_body(body: str) -> bool:
    """Accept only a reductional ``rfl`` proof and enclosing namespace ends."""
    clean = blank_comments(body)
    assignment = clean.find(":=")
    if assignment < 0:
        return False
    return re.fullmatch(
        r"\s*:=\s*(?:by\s+)?rfl\s*(?:end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*)*",
        clean[assignment:],
    ) is not None


def replace_references(body: str, mappings: list[dict[str, str]]) -> str:
    """Perform only unambiguous terminal-name rewrites in a candidate body."""
    terminals = [record["source"].rsplit(".", 1)[-1] for record in mappings]
    if len(terminals) != len(set(terminals)):
        raise RemapError("cannot transplant mappings with ambiguous local terminal names")
    rewritten = body
    for record in sorted(mappings, key=lambda item: len(item["source"]), reverse=True):
        source = record["source"]
        canonical = record["canonical"]
        rewritten = re.sub(rf"(?<![A-Za-z0-9_.']){re.escape(source)}(?![A-Za-z0-9_.'])",
                           canonical, rewritten)
        short_source = source.rsplit(".", 1)[-1]
        short_canonical = canonical.rsplit(".", 1)[-1]
        rewritten = re.sub(rf"(?<![A-Za-z0-9_']){re.escape(short_source)}(?![A-Za-z0-9_'])",
                           short_canonical, rewritten)
    return rewritten


def emit_transplant(path: Path, report: dict[str, Any],
                    target_declarations: list[tuple[dict[str, Any], dict[str, Any]]],
                    mappings: list[dict[str, str]]) -> None:
    lines = [
        "-- PM-INTERFACE-ONLY-TRANSPLANT",
        "-- This is a candidate body bundle, not a canonical integration or CI result.",
        f"-- Archive SHA-256: {report['archive']['sha256']}",
        f"-- Report SHA-256: {sha256_text(json.dumps(report, ensure_ascii=False, sort_keys=True))}",
        "",
    ]
    for target, declaration in target_declarations:
        canonical_namespace, _ = target["canonical"].rsplit(".", 1)
        lines.append(f"namespace {canonical_namespace}")
        lines.append("")
        lines.append(replace_references(declaration["body"], mappings).rstrip())
        lines.append("")
        lines.append(f"end {canonical_namespace}")
        lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def run_remap(root: Path, batch: str, archive: Path | None = None,
              mapping_path: Path | None = None, transplant: Path | None = None) -> dict[str, Any]:
    plan = batch_plan(root, batch)
    report: dict[str, Any] = {
        "kind": "pm-interface-kernel-remap-report",
        "batch": batch,
        "policy": {
            "canonical_integration_forbidden": True,
            "requires_one_to_one_kernel_remap": True,
            "no_local_lean_or_ci_was_run": True,
        },
        "plan": plan,
        "status": "blocked",
        "reasons": [],
    }
    try:
        mappings = load_mapping(mapping_path)
    except (OSError, json.JSONDecodeError, RemapError) as error:
        mappings = []
        report["reasons"].append(f"invalid mapping: {error}")
    if batch in RFL_ONLY_INSERTION_BATCHES and mappings:
        report["reasons"].append(f"{batch} forbids dependency mappings")
    # A target marked for insertion is intentionally absent from the edition;
    # only mapped dependencies and non-insertion targets must already resolve.
    canonical_names = {target["canonical"] for target in plan["targets"]
                       if not target.get("insertion_target", False)}
    canonical_names.update(record["canonical"] for record in mappings)
    canonical = find_canonical_declarations(root, canonical_names)
    report["canonical_declarations"] = [
        {
            "declaration": target["canonical"],
            "role": "target-insertion" if target.get("insertion_target") else "dependency-or-existing-target",
            "exists": target["canonical"] in canonical,
            "expected_signature_sha256": target["signature_sha256"],
            "actual_signature_sha256": canonical.get(target["canonical"], {}).get("signature_sha256"),
        }
        for target in plan["targets"]
    ]
    for record in report["canonical_declarations"]:
        if record["role"] == "target-insertion":
            continue
        if not record["exists"]:
            report["reasons"].append(f"missing canonical declaration {record['declaration']}")
        elif record["expected_signature_sha256"] != record["actual_signature_sha256"]:
            report["reasons"].append(f"canonical signature mismatch {record['declaration']}")
    if archive is None:
        default = root / "aristotle/results" / f"{batch}-final.tar.gz"
        report["archive"] = {"path": str(default), "present": False,
                             "expected_sha256": plan["archive_sha256"]}
        report["reasons"].append("terminal archive unavailable")
        return report
    try:
        digest, files, declarations, forbidden, imports = archive_sources(archive)
    except (OSError, tarfile.TarError, RemapError) as error:
        report["archive"] = {"path": str(archive), "present": False,
                             "expected_sha256": plan["archive_sha256"]}
        report["reasons"].append(str(error))
        return report
    report["archive"] = {"path": str(archive), "present": True, "sha256": digest,
                         "expected_sha256": plan["archive_sha256"], "lean_files": files}
    if plan["archive_sha256"] is None:
        report["reasons"].append("no audited immutable archive SHA-256 is registered")
    elif digest != plan["archive_sha256"]:
        report["reasons"].append("archive SHA-256 mismatch")
    report["forbidden_constructs"] = forbidden
    report["reasons"].extend(forbidden)
    if batch in RFL_ONLY_INSERTION_BATCHES:
        report["archive_dependencies"] = imports
        if imports:
            report["reasons"].append(
                f"{batch} forbids archive dependencies/imports: " + "; ".join(imports)
            )
    mapped = {record["source"]: record["canonical"] for record in mappings}
    # The audited targets always have a mandatory mapping, even when their
    # archive namespace happens to equal the canonical namespace.
    for target in plan["targets"]:
        mapped.setdefault(target["source"], target["canonical"])
    if len(set(mapped.values())) != len(mapped):
        report["reasons"].append("mapping is not one-to-one after target mappings")
    source_by_name = {record["qualified"]: record for record in declarations}
    if len(source_by_name) != len(declarations):
        report["reasons"].append("duplicate local declaration names in archive")
    unmapped = sorted(set(source_by_name) - set(mapped))
    if unmapped:
        report["reasons"].append("unmapped local declarations: " + ", ".join(unmapped))
    if batch in {"Q296", *STRICT_INSERTION_BATCHES}:
        target_sources = {target["source"] for target in plan["targets"]}
        local_declarations = sorted(set(source_by_name) - target_sources)
        if local_declarations:
            report["reasons"].append(
                f"{batch} forbids archive-local declarations: " + ", ".join(local_declarations)
            )
        forbidden_kinds = sorted(
            declaration["qualified"] for declaration in declarations
            if declaration["kind"] in {"axiom", "opaque"}
        )
        if forbidden_kinds:
            report["reasons"].append(
                f"{batch} forbids axiom/opaque declarations: " + ", ".join(forbidden_kinds)
            )
    mapped_records: list[dict[str, Any]] = []
    for source_name, canonical_name in sorted(mapped.items()):
        source = source_by_name.get(source_name)
        canonical_record = canonical.get(canonical_name)
        insertion = any(target["source"] == source_name and target.get("insertion_target")
                        for target in plan["targets"])
        item: dict[str, Any] = {
            "source": source_name,
            "canonical": canonical_name,
            "source_present": source is not None,
            "canonical_present": canonical_record is not None,
            "role": "target-insertion" if insertion else "dependency-mapping",
        }
        if source is None:
            report["reasons"].append(f"mapped source declaration absent: {source_name}")
        else:
            item["source_signature_sha256"] = source["signature_sha256"]
        if canonical_record is None:
            if not insertion:
                report["reasons"].append(f"mapped canonical declaration absent: {canonical_name}")
        else:
            item["canonical_signature_sha256"] = canonical_record["signature_sha256"]
        if source is not None and canonical_record is not None and (
                source["signature_sha256"] != canonical_record["signature_sha256"]):
            report["reasons"].append(f"signature mismatch {source_name} -> {canonical_name}")
        mapped_records.append(item)
    report["declaration_mappings"] = mapped_records
    targets_found: list[dict[str, Any]] = []
    for target in plan["targets"]:
        source = source_by_name.get(target["source"])
        exact = source is not None and source["signature_sha256"] == target["signature_sha256"]
        targets_found.append({
            "id": target["id"], "source": target["source"], "canonical": target["canonical"],
            "expected_signature_sha256": target["signature_sha256"],
            "actual_signature_sha256": source.get("signature_sha256") if source else None,
            "exact_signature": exact,
            "role": "target-insertion" if target.get("insertion_target") else "existing-target",
            "body_policy": target.get("body_policy"),
        })
        if not exact:
            report["reasons"].append(f"target signature mismatch or absent: {target['source']}")
        if target.get("body_policy") == "rfl-only" and (
                source is None or not is_rfl_only_body(source["body"])):
            report["reasons"].append(f"target body is not rfl-only: {target['source']}")
    report["targets"] = targets_found
    report["reasons"] = sorted(set(report["reasons"]))
    if not report["reasons"]:
        report["status"] = "transplantable-interface-only"
        report["transplant"] = {
            "allowed": True,
            "promotion": "forbidden",
            "requires_independent_remote_kernel_check": True,
        }
        if transplant is not None:
            target_declarations = [(target, source_by_name[target["source"]])
                                   for target in plan["targets"]]
            emit_transplant(transplant, report, target_declarations,
                            [{"source": source, "canonical": canonical}
                             for source, canonical in mapped.items()])
            report["transplant"]["path"] = str(transplant)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("batch", choices=SUPPORTED_BATCHES)
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--mapping", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--transplant", type=Path)
    options = parser.parse_args()
    report = run_remap(ROOT, options.batch, options.archive, options.mapping, options.transplant)
    rendered = json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if options.report:
        options.report.parent.mkdir(parents=True, exist_ok=True)
        options.report.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    if report["status"] != "transplantable-interface-only":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
