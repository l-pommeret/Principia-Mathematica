#!/usr/bin/env python3
"""Verify that operational retry QIDs cannot become duplicate PM promotions."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "metadata/retry_registry.json"
SCHEMA = ROOT / "metadata/schema/retry-registry.schema.json"
PIPELINE = ROOT / "pipeline.json"
QID = re.compile(r"^Q(\d+)$")


def fail(message: str) -> None:
    print(f"retry registry error: {message}", file=sys.stderr)
    raise SystemExit(1)


def verify(path: Path = REGISTRY) -> dict:
    if not SCHEMA.is_file():
        fail("retry registry schema is missing")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))
    if data.get("kind") != "pm-operational-retry-registry" or data.get("schema_version") != 1:
        fail("invalid registry header")
    policy = data.get("policy", {})
    required_policy = {
        "retry_is_not_a_new_item": True,
        "retry_promotes_only_its_canonical_batch": True,
        "one_open_retry_per_canonical_batch": True,
    }
    if any(policy.get(key) != value for key, value in required_policy.items()):
        fail("canonical-promotion policy is incomplete")
    retries = data.get("retries")
    if not isinstance(retries, list) or not retries:
        fail("retries must be a non-empty list")
    qids, canonicals = set(), set()
    try:
        questions = json.loads(PIPELINE.read_text(encoding="utf-8")).get("questions", {})
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read pipeline retry records: {error}")
    for retry in retries:
        required = {"qid", "retry_of", "followup", "state", "promotion_key"}
        if not isinstance(retry, dict) or required - retry.keys():
            fail("retry record lacks required fields")
        qid, canonical = retry["qid"], retry["retry_of"]
        match = QID.fullmatch(qid)
        if not match or int(match.group(1)) < policy.get("retry_qid_minimum", 9001):
            fail(f"{qid}: retry QID must be Q9001 or later")
        if not QID.fullmatch(canonical) or int(QID.fullmatch(canonical).group(1)) >= 9001:
            fail(f"{qid}: retry_of must be a canonical, non-retry QID")
        if qid in qids or canonical in canonicals:
            fail(f"{qid}: duplicate retry QID or canonical promotion key")
        if retry["promotion_key"] != canonical:
            fail(f"{qid}: promotion_key must equal retry_of, never the retry QID")
        pipeline_retry = questions.get(qid)
        if not isinstance(pipeline_retry, dict):
            fail(f"{qid}: retry is missing from pipeline.json")
        if (pipeline_retry.get("retry_of") != canonical
                or pipeline_retry.get("promotion_key") != canonical
                or pipeline_retry.get("canonical_promotion_forbidden") is not True):
            fail(f"{qid}: pipeline retry identity is not canonical-only")
        if pipeline_retry.get("canonical_ids") or pipeline_retry.get("integration_status"):
            fail(f"{qid}: an operational retry must not own formal items or promotion status")
        if not isinstance(questions.get(canonical), dict):
            fail(f"{qid}: canonical batch {canonical} is absent from pipeline.json")
        followup = ROOT / retry["followup"]
        if not followup.is_file():
            fail(f"{qid}: followup is missing: {retry['followup']}")
        qids.add(qid)
        canonicals.add(canonical)
    return data


if __name__ == "__main__":
    registry = verify()
    print(f"retry registry checks passed ({len(registry['retries'])} operational retries)")
