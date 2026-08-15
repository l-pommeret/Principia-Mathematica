#!/usr/bin/env python3
"""The gates decide what may be called certified; they must not drift silently.

Every other gate in this repository judges the edition.  Nothing judged the
gates.  That asymmetry is the one an editor should worry about most: a gate is
the cheapest thing to weaken when it is inconvenient, and weakening one costs
nothing at the moment it happens while invalidating every certification made
afterwards.  This repository has already seen 969 items marked certified that
were not; the lesson was that a claim nobody can re-derive is worth nothing.

So each gate script is pinned here by SHA-256, and this check runs before any
other.  What it buys is precise and worth stating exactly:

* A gate edited by accident — or by an agent that found it easier to change the
  rule than to satisfy it — fails the build immediately, naming the file.
* A gate edited on purpose still passes, but only after the gate itself has been
  committed and its digest is updated in ``metadata/gate_integrity.json`` by a
  separate, expressly authorised commit.  The digest is computed from HEAD,
  never from uncommitted bytes that could make the check approve itself.

What it does not buy: this is tamper-evident, not tamper-proof.  Anyone who can
edit a gate can also run ``--update``.  The protection is that they cannot do it
*quietly* — and combined with branch protection and CODEOWNERS review on
``scripts/verify_*``, a change to the standard becomes a decision someone signs
for rather than a line that slips through.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "metadata" / "gate_integrity.json"

#: Files whose content defines the standard.  Everything a gate imports belongs
#: here too: pinning `verify_certification_tier.py` while leaving
#: `pm_lean_index.py` free would pin the judge and release the evidence.
PROTECTED_GLOBS = (
    "scripts/verify_*.py",
    "scripts/derive_certification_registry.py",
    "scripts/pm_lean_index.py",
    "scripts/promote_awaiting_ci.py",
    # Exemption registries, workflow success conditions, and gate tests extend
    # the certification standard; they are normative inputs, not ordinary data.
    "metadata/two_sided_exemptions.json",
    "metadata/printed_witness_exemptions.json",
    "metadata/catalogue_completeness_exemptions.json",
    # The durable witnesses are the bytes judged by the printed-reading gate;
    # leaving them mutable would protect the judge while releasing its evidence.
    "metadata/witnesses/gutenberg/pg*-tex.txt",
    "metadata/judgement_constructors.json",
    "metadata/assumptions.json",
    "metadata/dependency_aliases.json",
    "scripts/sync_item_printed.py",
    "scripts/report_lean_source_coverage.py",
    "scripts/build_edition.py",
    "docs/certification_registry.json",
    "tests/*.py",
    "tests/**/*.py",
    "tests/**/*.lean",
)

#: This script is pinned like the rest — a check that exempts itself protects
#: nothing — but its own digest is compared last, so that a tampered integrity
#: checker still reports the gates it was asked to protect before reporting
#: itself.
SELF = "scripts/verify_gate_integrity.py"


def protected_files() -> list[Path]:
    found: set[Path] = set()
    for pattern in PROTECTED_GLOBS:
        found.update(ROOT.glob(pattern))
    return sorted(found)


def _is_protected(name: str) -> bool:
    path = Path(name)
    return any(path.match(pattern) for pattern in PROTECTED_GLOBS)


def _protected_tree_roots() -> tuple[str, ...]:
    """Return the narrowest top-level Git pathspecs covering every glob."""
    roots: set[str] = set()
    for pattern in PROTECTED_GLOBS:
        root = Path(pattern).parts[0]
        if any(character in root for character in "*?["):
            return (".",)
        roots.add(root)
    return tuple(sorted(roots))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def current() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): digest(path) for path in protected_files()
    }


def _git(
    *arguments: str,
    check: bool = True,
    input_data: bytes | None = None,
) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        ["git", *arguments],
        cwd=ROOT,
        input=input_data,
        capture_output=True,
        check=False,
    )
    if check and result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return result


def _git_blob(revision: str, name: str) -> bytes | None:
    result = _git("show", f"{revision}:{name}", check=False)
    return result.stdout if result.returncode == 0 else None


def _git_blob_digests(entries: list[tuple[str, str]]) -> dict[str, str]:
    """Hash Git blobs in one batch instead of spawning once per protected file."""
    if not entries:
        return {}
    queries = b"".join(f"{object_id}\n".encode("ascii") for _, object_id in entries)
    output = _git("cat-file", "--batch", input_data=queries).stdout
    digests: dict[str, str] = {}
    offset = 0
    for name, expected_id in entries:
        header_end = output.find(b"\n", offset)
        if header_end < 0:
            raise RuntimeError("git cat-file --batch returned a truncated header")
        fields = output[offset:header_end].split()
        if len(fields) != 3 or fields[0].decode("ascii") != expected_id:
            raise RuntimeError("git cat-file --batch returned an unexpected object")
        if fields[1] != b"blob":
            raise RuntimeError(f"git object for {name} is not a blob")
        size = int(fields[2])
        content_start = header_end + 1
        content_end = content_start + size
        if output[content_end : content_end + 1] != b"\n":
            raise RuntimeError("git cat-file --batch returned truncated content")
        digests[name] = digest_bytes(output[content_start:content_end])
        offset = content_end + 1
    return digests


def committed_at(revision: str) -> dict[str, str]:
    """Return protected digests from a commit, never the worktree."""
    listing = _git(
        "ls-tree",
        "-r",
        "-z",
        revision,
        "--",
        *_protected_tree_roots(),
    )
    entries: list[tuple[str, str]] = []
    for record in listing.stdout.rstrip(b"\0").split(b"\0"):
        if not record:
            continue
        metadata, raw_name = record.split(b"\t", 1)
        _, object_type, raw_object_id = metadata.split(b" ", 2)
        name = raw_name.decode("utf-8")
        if object_type == b"blob" and _is_protected(name):
            entries.append((name, raw_object_id.decode("ascii")))
    return _git_blob_digests(entries)


def head_current() -> dict[str, str]:
    return committed_at("HEAD")


def head_oid() -> str:
    return _git("rev-parse", "HEAD").stdout.decode("ascii").strip()


def _payload(content: bytes) -> dict[str, object]:
    return json.loads(content.decode("utf-8"))


def head_payload() -> dict[str, object]:
    content = _git_blob("HEAD", str(MANIFEST.relative_to(ROOT)))
    return _payload(content) if content is not None else {}


def differences(now: dict[str, str], before: dict[str, str]) -> list[str]:
    problems: list[str] = []
    for name in sorted(set(before) - set(now)):
        problems.append(
            f"{name}: pinned gate has been deleted. A standard is not retired by "
            "removing the file that enforces it; drop it from the manifest in the "
            "same commit, and say why in the message"
        )
    for name in sorted(set(now) - set(before)):
        problems.append(
            f"{name}: new gate is unpinned. Run "
            "`python3 scripts/verify_gate_integrity.py --update` and commit the "
            "manifest alongside it"
        )
    for name in sorted(set(now) & set(before)):
        if now[name] != before[name]:
            problems.append(
                f"{name}: content changed but the pinned digest did not "
                f"({before[name][:12]} -> {now[name][:12]}). If the change is "
                "intended, `--update` records it and the diff will show that this "
                "commit altered what counts as proof"
            )
    return sorted(problems, key=lambda line: line.startswith(SELF))


def manifest_head_differences(
    committed: dict[str, str], pinned: dict[str, str]
) -> list[str]:
    """Compare the proposed manifest with the only auditable source: HEAD."""
    problems: list[str] = []
    for name in sorted(set(pinned) - set(committed)):
        problems.append(
            f"{name}: le manifeste épingle un gate absent de HEAD. Un fichier "
            "non commité n'est pas une base d'autorisation vérifiable ; commitez "
            "d'abord le gate, puis ré-épinglez-le dans un commit séparé"
        )
    for name in sorted(set(committed) - set(pinned)):
        problems.append(
            f"{name}: ce gate existe dans HEAD mais n'est pas épinglé par le "
            "manifeste. Lancez --update seulement après avoir commité le gate"
        )
    for name in sorted(set(committed) & set(pinned)):
        if committed[name] != pinned[name]:
            problems.append(
                f"{name}: l'empreinte épinglée {pinned[name][:12]} ne correspond "
                f"pas au contenu connu de HEAD {committed[name][:12]}. "
                "L'autorisation doit viser un gate déjà commité"
            )
    return sorted(problems, key=lambda line: line.startswith(SELF))


def manifest_changed_from_head() -> bool:
    committed = _git_blob("HEAD", str(MANIFEST.relative_to(ROOT)))
    if not MANIFEST.is_file():
        return committed is not None
    return committed != MANIFEST.read_bytes()


def worktree_head_differences(
    committed: dict[str, str], manifest_changed: bool
) -> list[str]:
    """Reject protected bytes that have not yet acquired a commit identity."""
    worktree = current()
    problems: list[str] = []
    for name in sorted(set(worktree) - set(committed)):
        suffix = (
            " Le manifeste change lui aussi : ré-épingler ces octets dans le "
            "même geste rendrait le contrôle vide (vacuous)."
            if manifest_changed
            else ""
        )
        problems.append(
            f"{name}: gate présent dans le répertoire mais absent de HEAD ; il "
            f"n'est donc pas encore autorisable.{suffix} Commitez d'abord le "
            "gate, puis modifiez seulement le manifeste dans un commit séparé"
        )
    for name in sorted(set(committed) - set(worktree)):
        problems.append(
            f"{name}: gate suivi dans HEAD mais absent du répertoire de travail"
        )
    for name in sorted(set(committed) & set(worktree)):
        if committed[name] != worktree[name]:
            if manifest_changed:
                problems.append(
                    f"{name}: le gate et le manifeste diffèrent tous deux de "
                    "HEAD. Ré-épingler le gate en même temps que sa modification "
                    "rend le contrôle vide (vacuous) : l'empreinte ne ferait que "
                    "confirmer les octets qu'on vient de lui donner. Commitez "
                    "d'abord le gate, puis lancez --update et commitez seulement "
                    "le manifeste"
                )
            else:
                problems.append(
                    f"{name}: le gate diffère de HEAD. Commitez cette modification "
                    "avant toute ré-autorisation ; --update ne lit que HEAD"
                )
    return sorted(problems, key=lambda line: line.startswith(SELF))


def committed_cochanges() -> list[str]:
    """Find gates changed with the manifest by the current HEAD commit."""
    revision = _git("rev-list", "--parents", "-n", "1", "HEAD")
    commits = revision.stdout.decode("ascii").split()
    if len(commits) < 2:  # The root commit establishes the initial trust base.
        return []
    parent = commits[1]
    changed = _git(
        "diff",
        "--name-only",
        "-z",
        parent,
        "HEAD",
        "--",
        str(MANIFEST.relative_to(ROOT)),
        "scripts",
    ).stdout.decode("utf-8").rstrip("\0").split("\0")
    if str(MANIFEST.relative_to(ROOT)) not in changed:
        return []
    gates = sorted(name for name in changed if _is_protected(name))
    return [
        f"{name}: ce gate et metadata/gate_integrity.json ont changé dans le "
        "même commit HEAD. Cette ré-autorisation est suspecte : ré-épingler en "
        "même temps que la modification rend le contrôle vide (vacuous). Le "
        "gate doit être commité d'abord, puis --update et le manifeste doivent "
        "faire l'objet d'un commit séparé"
        for name in gates
    ]


def authorisation_boundary_problems(
    payload: dict[str, object], pinned: dict[str, str], manifest_changed: bool
) -> list[str]:
    """Verify the durable commit boundary recorded by the latest --update."""
    history = payload.get("authorisations", [])
    if not isinstance(history, list) or not history:
        return [
            "metadata/gate_integrity.json: aucune autorisation journalisée ne "
            "permet de relier les empreintes à un snapshot Git"
        ]
    latest = history[-1]
    authorised = latest.get("authorised_head") if isinstance(latest, dict) else None
    if not isinstance(authorised, str) or not authorised:
        return [
            "metadata/gate_integrity.json: la dernière autorisation ne contient "
            "pas authorised_head. Elle précède le protocole vérifiable contre "
            "HEAD ; après avoir commité les gates, relancez --update dans un "
            "commit séparé"
        ]

    resolved = _git("rev-parse", "--verify", f"{authorised}^{{commit}}", check=False)
    if resolved.returncode:
        return [
            "metadata/gate_integrity.json: authorised_head ne désigne pas un "
            f"commit disponible ({authorised})"
        ]
    authorised = resolved.stdout.decode("ascii").strip()
    ancestor = _git("merge-base", "--is-ancestor", authorised, "HEAD", check=False)
    if ancestor.returncode:
        return [
            "metadata/gate_integrity.json: authorised_head n'est pas un ancêtre "
            "de HEAD ; l'autorisation n'est pas vérifiable dans cet historique"
        ]

    snapshot = committed_at(authorised)
    problems: list[str] = []
    for name in sorted(set(pinned) | set(snapshot)):
        if name not in snapshot:
            problems.append(
                f"{name}: absent du snapshot autorisé {authorised[:12]}"
            )
        elif name not in pinned:
            problems.append(
                f"{name}: présent dans le snapshot autorisé mais absent du manifeste"
            )
        elif pinned[name] != snapshot[name]:
            problems.append(
                f"{name}: l'empreinte du manifeste ne correspond pas au snapshot "
                f"autorisé {authorised[:12]}"
            )

    current_head = head_oid()
    if authorised == current_head:
        if not manifest_changed:
            problems.append(
                "metadata/gate_integrity.json: authorised_head est le commit qui "
                "contient déjà le manifeste. Une autorisation valide pointe le "
                "commit antérieur qui contient les gates, puis le manifeste est "
                "commité séparément"
            )
        return problems

    changed = _git(
        "diff",
        "--name-only",
        "-z",
        authorised,
        "HEAD",
        "--",
        str(MANIFEST.relative_to(ROOT)),
        "scripts",
    ).stdout.decode("utf-8").rstrip("\0").split("\0")
    manifest_name = str(MANIFEST.relative_to(ROOT))
    if manifest_name not in changed:
        problems.append(
            "metadata/gate_integrity.json: aucun commit du manifeste ne suit "
            "authorised_head ; la séparation gate puis autorisation est absente"
        )
    for name in sorted(path for path in changed if _is_protected(path)):
        problems.append(
            f"{name}: ce gate a changé après le snapshot autorisé "
            f"{authorised[:12]} et dans l'intervalle qui contient le manifeste. "
            "Gate et ré-épinglage ne sont donc pas séparés de façon vérifiable"
        )
    return problems


#: ANSI escapes, used only when stderr is a terminal.  A gate failure that
#: scrolls past unnoticed is a gate that does not exist.
_RED = "\033[1;31m"
_YELLOW = "\033[1;33m"
_RESET = "\033[0m"


def _colour(text: str, escape: str) -> str:
    return f"{escape}{text}{_RESET}" if sys.stderr.isatty() else text


def _banner(lines: list[str], escape: str = _RED) -> None:
    wrapped: list[str] = []
    for line in lines:
        wrapped.extend(textwrap.wrap(line, width=64) or [""])
    width = max(len(line) for line in wrapped) + 4
    print(_colour("╔" + "═" * width + "╗", escape), file=sys.stderr)
    for line in wrapped:
        print(
            _colour(f"║  {line.ljust(width - 4)}  ║", escape),
            file=sys.stderr,
        )
    print(_colour("╚" + "═" * width + "╝", escape), file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update",
        action="store_true",
        help=(
            "re-pin every protected file to its content in HEAD. Refused unless "
            "--authorised-by and --reason are both given: changing a gate changes "
            "what counts as a proof of Principia Mathematica, and that is the "
            "editor's decision, not a build step"
        ),
    )
    parser.add_argument(
        "--authorised-by",
        metavar="NAME",
        help="the editor who expressly authorised this change of standard",
    )
    parser.add_argument(
        "--reason",
        metavar="TEXT",
        help="why the standard is being changed (recorded in the manifest)",
    )
    parser.add_argument("--report-all", action="store_true")
    arguments = parser.parse_args()

    if arguments.update and not (arguments.authorised_by and arguments.reason):
        _banner([
            "REFUSÉ — modification du standard non autorisée",
            "",
            "Re-pinning the gates changes what may be called a derivation",
            "of PM. It requires the editor's express authorisation:",
            "",
            "  --authorised-by <name> --reason <why>",
            "",
            "Both are recorded in metadata/gate_integrity.json and travel",
            "in the commit, so the change of standard is signed for.",
        ])
        return 2

    files = protected_files()
    if not files:
        print(
            "no gate script found; the integrity check would pass vacuously",
            file=sys.stderr,
        )
        return 1

    try:
        committed = head_current()
    except RuntimeError as error:
        print(f"cannot verify gate integrity against HEAD: {error}", file=sys.stderr)
        return 1

    if arguments.update:
        update_problems = worktree_head_differences(
            committed, manifest_changed=manifest_changed_from_head()
        )
        if manifest_changed_from_head():
            update_problems.insert(
                0,
                "metadata/gate_integrity.json diffère déjà de HEAD. --update "
                "refuse de prendre un manifeste de travail comme base : "
                "conservez ou annulez d'abord ces changements explicitement",
            )
        if update_problems:
            _banner([
                "REFUSÉ — HEAD N'EST PAS UNE BASE D'AUTORISATION PROPRE",
                "",
                "Ré-épingler un gate dans le même geste que sa modification",
                "rend le contrôle vide (vacuous). Commitez d'abord le gate,",
                "puis, depuis un worktree de gates propre, lancez --update et",
                "commitez seulement metadata/gate_integrity.json.",
            ])
            shown = update_problems if arguments.report_all else update_problems[:10]
            for problem in shown:
                print(_colour(f"  {problem}", _RED), file=sys.stderr)
            if len(update_problems) > len(shown):
                print(
                    _colour(
                        f"  ... and {len(update_problems) - len(shown)} more", _RED
                    ),
                    file=sys.stderr,
                )
            return 1

        before_payload = head_payload()
        before = before_payload.get("digests", {})
        changed = differences(committed, before) if before else []
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        history = before_payload.get("authorisations", [])
        assert isinstance(history, list)
        history.append(
            {
                "authorised_by": arguments.authorised_by,
                "authorised_head": head_oid(),
                "reason": arguments.reason,
                "scripts_changed": [line.split(":")[0] for line in changed],
            }
        )
        MANIFEST.write_text(
            json.dumps(
                {
                    "note": (
                        "SHA-256 of every script that defines the certification "
                        "standard. Changing a gate is legitimate; changing one "
                        "without updating this file is not, and the preflight "
                        "refuses it. A gate must be committed first; a separate "
                        "authorised commit then re-pins its HEAD content. Every "
                        "re-pinning records who authorised it and why."
                    ),
                    "authorisations": history,
                    "digests": committed,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        _banner(
            [
                "STANDARD MODIFIÉ — autorisé par "
                + str(arguments.authorised_by),
                "",
                f"raison : {arguments.reason}",
                f"scripts re-épinglés : {len(changed) or len(committed)}",
            ],
            _YELLOW,
        )
        print(
            f"pinned {len(committed)} gate scripts in {MANIFEST.relative_to(ROOT)}"
        )
        return 0

    before_payload = _payload(MANIFEST.read_bytes()) if MANIFEST.is_file() else {}
    before = before_payload.get("digests", {})
    if not before:
        print(
            f"{MANIFEST.relative_to(ROOT)} is missing: the gates are unpinned. "
            "Run `python3 scripts/verify_gate_integrity.py --update`.",
            file=sys.stderr,
        )
        return 1

    problems = manifest_head_differences(committed, before)
    problems.extend(
        worktree_head_differences(
            committed, manifest_changed=manifest_changed_from_head()
        )
    )
    problems.extend(committed_cochanges())
    problems.extend(
        authorisation_boundary_problems(
            before_payload, before, manifest_changed=manifest_changed_from_head()
        )
    )
    if problems:
        _banner([
            "ALERTE — RÉ-AUTORISATION DE GATE NON VÉRIFIABLE",
            "",
            f"{len(problems)} anomalie(s) entre le manifeste, HEAD et le worktree.",
            "",
            "Ré-épingler un gate dans le même commit que sa modification",
            "rend le contrôle vide (vacuous) : la nouvelle empreinte ne",
            "prouve rien d'autre que le contenu qui vient de la produire.",
            "",
            "À faire : commitez d'abord le gate sans toucher au manifeste.",
            "Puis, dans un commit séparé, faites autoriser le contenu de HEAD :",
            "  python3 scripts/verify_gate_integrity.py --update \\",
            "      --authorised-by <nom> --reason <pourquoi>",
            "Et commitez seulement metadata/gate_integrity.json.",
        ])
        shown = problems if arguments.report_all else problems[:10]
        for problem in shown:
            print(_colour(f"  {problem}", _RED), file=sys.stderr)
        if len(problems) > len(shown):
            print(
                _colour(f"  ... and {len(problems) - len(shown)} more", _RED),
                file=sys.stderr,
            )
        return 1

    print(
        "gate integrity verified "
        f"({len(committed)} HEAD scripts match their pinned digests)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
