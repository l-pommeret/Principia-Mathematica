#!/usr/bin/env python3
"""Report the deterministic PM-to-Aristotle reconstruction frontier.

This is intentionally an inventory, not a source harvester.  It reports only
items that are already catalogued under ``metadata/items`` and never turns a
prompt or a planned campaign question into a claim that the corresponding PM
statement has been transcribed or parsed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import aristotle_scheduler
from pm_constraint_manifest import load_item_registry
from pm_proof_skeleton import parse_demonstration
from pm_syntax import parse_statement
from verify_dependencies import load_items


METALINGUISTIC_KINDS = {
    "derived-metalinguistic-rule",
    "primitive-inference-rule",
    "primitive-function-inference-rule",
    "primitive-formation-rule",
}
PM_SECTION_RE = re.compile(r"^(PM\d+):✱(\d+)·")


class QueueInventoryError(ValueError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise QueueInventoryError(f"{path}: expected a JSON object")
    return value


def count_by_section(identifiers: set[str] | list[str]) -> dict[str, int]:
    result: Counter[str] = Counter()
    for identifier in identifiers:
        match = PM_SECTION_RE.match(identifier)
        if match:
            result[f"{match.group(1)}:✱{match.group(2)}"] += 1
    return dict(sorted(result.items()))


def batch_index(root: Path) -> tuple[dict[str, dict], dict[str, dict]]:
    """Return item and batch records derived solely from reviewed batch specs."""
    by_item: dict[str, dict] = {}
    batches: dict[str, dict] = {}
    for spec_path in sorted((root / "metadata/constrained_batches").glob("*.json")):
        spec = read_json(spec_path)
        if spec.get("kind") != "pm-constrained-batch-spec":
            raise QueueInventoryError(f"{spec_path}: not a constrained batch spec")
        batch = spec_path.stem
        manifest_path = root / "aristotle/manifests" / f"{batch}.json"
        context_path = root / "aristotle/contexts" / f"{batch}.lean"
        bundle_path = root / "metadata/context_bundles" / f"{batch}.json"
        prompt_path = root / spec.get("prompt_path", "")
        targets: list[str] = []
        for entry in spec.get("items", []):
            if not isinstance(entry, dict) or not isinstance(entry.get("id"), str):
                raise QueueInventoryError(f"{spec_path}: invalid batch item")
            identifier = entry["id"]
            if identifier in by_item:
                raise QueueInventoryError(
                    f"{identifier}: appears in both {by_item[identifier]['batch']} and {batch}"
                )
            demonstration_path = root / entry.get("demonstration_path", "")
            if not demonstration_path.is_file():
                raise QueueInventoryError(f"{identifier}: missing {demonstration_path}")
            # Parsing here ensures the inventory's "skeleton" column is
            # evidence, rather than merely the presence of a text file.
            parse_demonstration(
                demonstration_path.read_text(encoding="utf-8"),
                spec.get("volume", 1),
                identifier,
            )
            record = {
                "batch": batch,
                "generation_status": spec.get("generation_status", "ready"),
                "demonstration_path": str(demonstration_path.relative_to(root)),
                "demonstration_sha256": sha256(demonstration_path),
                "manifest": manifest_path.is_file(),
                "context": context_path.is_file(),
                "context_metadata": bundle_path.is_file(),
                "prompt": prompt_path.is_file(),
            }
            by_item[identifier] = record
            targets.append(identifier)
        batches[batch] = {
            "generation_status": spec.get("generation_status", "ready"),
            "targets": targets,
            "manifest": manifest_path.is_file(),
            "context": context_path.is_file(),
            "context_metadata": bundle_path.is_file(),
            "prompt": prompt_path.is_file(),
        }
    return by_item, batches


def inventory(root: Path = ROOT) -> dict:
    catalogue = load_items(root)
    registry = load_item_registry(root / "metadata/items")
    if len(catalogue) != len(registry):
        raise QueueInventoryError("catalogue and item registry disagree")
    by_batch_item, batches = batch_index(root)
    pipeline = read_json(root / "pipeline.json")
    questions = pipeline.get("questions", {})
    if not isinstance(questions, dict):
        raise QueueInventoryError("pipeline questions must be an object")

    question_ids_by_item: defaultdict[str, list[str]] = defaultdict(list)
    planned_ids: set[str] = set()
    questions_by_audit_status: Counter[str] = Counter()
    questions_by_aristotle_status: Counter[str] = Counter()
    for qid, question in sorted(questions.items()):
        if not isinstance(question, dict):
            raise QueueInventoryError(f"{qid}: pipeline question must be an object")
        questions_by_audit_status[str(question.get("audit_status", "missing"))] += 1
        questions_by_aristotle_status[str(question.get("aristotle_status", "missing"))] += 1
        canonical_ids = question.get("canonical_ids", [])
        if not isinstance(canonical_ids, list) or not all(isinstance(i, str) for i in canonical_ids):
            raise QueueInventoryError(f"{qid}: canonical_ids must be a string list")
        for identifier in canonical_ids:
            question_ids_by_item[identifier].append(qid)
            planned_ids.add(identifier)

    records = []
    object_language = 0
    metalinguistic = 0
    for item in sorted(catalogue, key=lambda value: value["id"]):
        identifier = item["id"]
        record = {
            "id": identifier,
            "kind": item["kind"],
            "source_catalogue": True,
            "formal_status": item.get("formal_status", "unspecified"),
            "campaign_questions": question_ids_by_item.get(identifier, []),
        }
        if item["kind"] in METALINGUISTIC_KINDS:
            record["ast"] = {"status": "metalinguistic-route"}
            metalinguistic += 1
        else:
            ast = parse_statement(item["printed"])
            canonical = json.dumps(
                ast.to_dict(), ensure_ascii=False, sort_keys=True, separators=(",", ":")
            )
            record["ast"] = {
                "status": "parsed",
                "sha256": hashlib.sha256(canonical.encode("utf-8")).hexdigest(),
            }
            object_language += 1
        skeleton = by_batch_item.get(identifier)
        record["proof_skeleton"] = skeleton or {"status": "missing"}
        records.append(record)

    # The scheduler's candidate predicate is deliberately reused, but remote
    # active-task reconciliation is excluded: this is a local deterministic
    # backlog report, not a submission operation.
    local_candidates = aristotle_scheduler.candidates(pipeline, root, set())
    catalogued_ids = {item["id"] for item in catalogue}
    planned_uncatalogued = sorted(
        identifier for identifier in planned_ids - catalogued_ids
        if identifier.startswith("PM1:")
    )
    planned_non_pm_uncatalogued = sorted(
        identifier for identifier in planned_ids - catalogued_ids
        if not identifier.startswith("PM1:")
    )
    catalogued_without_campaign_question = sorted(catalogued_ids - planned_ids)
    uncatalogued_questions = {
        identifier: question_ids_by_item[identifier]
        for identifier in planned_uncatalogued
    }
    skeleton_catalogued = sum(item_id in catalogued_ids for item_id in by_batch_item)
    complete_batches = sum(
        batch["manifest"] and batch["context"] and batch["context_metadata"] and batch["prompt"]
        for batch in batches.values()
    )

    return {
        "kind": "pm-deterministic-queue-inventory",
        "scope": {
            "claim": "catalogued PM items only; no claim of coverage for untranscribed PM pages",
            "catalogue_directory": "metadata/items",
            "batch_spec_directory": "metadata/constrained_batches",
        },
        "counts": {
            "catalogued_items": len(records),
            "object_language_ast_parsed": object_language,
            "metalinguistic_routes": metalinguistic,
            "catalogued_items_with_proof_skeleton": skeleton_catalogued,
            "all_proof_skeleton_targets": len(by_batch_item),
            "catalogued_items_missing_proof_skeleton": len(records) - skeleton_catalogued,
            "constrained_batches": len(batches),
            "complete_batch_artifact_sets": complete_batches,
            "planned_campaign_questions": len(questions),
            "planned_uncatalogued_pm_ids": len(planned_uncatalogued),
            "planned_uncatalogued_non_pm_ids": len(planned_non_pm_uncatalogued),
            "catalogued_items_without_campaign_question": len(
                catalogued_without_campaign_question
            ),
            "locally_scheduler_eligible": len(local_candidates),
        },
        "question_statuses": {
            "audit": dict(sorted(questions_by_audit_status.items())),
            "aristotle": dict(sorted(questions_by_aristotle_status.items())),
        },
        "pm_section_coverage": {
            "catalogued": count_by_section(catalogued_ids),
            "planned": count_by_section(planned_ids),
            "planned_but_uncatalogued": count_by_section(planned_uncatalogued),
            "catalogued_without_campaign_question": count_by_section(
                catalogued_without_campaign_question
            ),
        },
        "local_scheduler_candidates": [
            {"question": candidate.qid, "kind": candidate.kind, "prompt_path": str(candidate.path.relative_to(root))}
            for candidate in local_candidates
        ],
        "batches": batches,
        "catalogued_items": records,
        "catalogued_not_yet_in_campaign": catalogued_without_campaign_question,
        "planned_but_uncatalogued": uncatalogued_questions,
        "planned_non_pm_but_uncatalogued": {
            identifier: question_ids_by_item[identifier]
            for identifier in planned_non_pm_uncatalogued
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="inventory the deterministic PM reconstruction queue"
    )
    outputs = parser.add_mutually_exclusive_group()
    outputs.add_argument(
        "--write",
        type=Path,
        help="write the canonical JSON report relative to the repository root",
    )
    outputs.add_argument(
        "--check",
        type=Path,
        help="fail if a generated JSON report differs from the inventory",
    )
    options = parser.parse_args()
    try:
        result = inventory()
    except (QueueInventoryError, ValueError, OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"PM queue inventory error: {error}") from error
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if options.write:
        destination = options.write
        if not destination.is_absolute():
            destination = ROOT / destination
        destination.write_text(rendered, encoding="utf-8")
    elif options.check:
        expected = options.check
        if not expected.is_absolute():
            expected = ROOT / expected
        if not expected.is_file() or expected.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"PM queue inventory drift: {expected}")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
