"""Shared assertion: a recorded status must equal the computed tier.

The kernel-gate tests used to hard-code `formal_status == "kernel-checked"` and
an exact `ci_evidence` dict, including the bare numeric run id that
`scripts/promote_awaiting_ci.py` would reject at argument parsing.  That made the
test suite enshrine the shape a bypassed promotion leaves behind: the tests could
only pass while the catalogue over-claimed.

They now assert the invariant that actually matters — whatever tier an item
records, the Lean tree must support it, and a certified item must carry evidence
that resolves.  The substantive checks in those files (printed dependencies,
explicit inference branches, cited demonstration steps) are untouched.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

RUN_URL = re.compile(r"https://github\.com/[^/]+/[^/]+/actions/runs/[0-9]+")


def assert_tier_consistent(test, metadata: dict, item: dict) -> None:
    """The item's recorded tier must be the one the Lean tree supports."""
    from verify_certification_tier import KNOWN_TIERS, compute
    from verify_ci_evidence import evidence_failures

    recorded = item.get("formal_status")
    test.assertIn(recorded, KNOWN_TIERS, f"{item.get('id')} records an unknown tier")

    reasons = evidence_failures(
        Path("metadata/items"), metadata.get("ci_evidence") or {}, metadata["items"]
    )
    tier, failed, notes = compute(item, reasons)
    test.assertEqual(
        recorded,
        tier,
        f"{item.get('id')} records {recorded!r} but the tree supports {tier!r}: "
        + "; ".join(f"{key}: {value}" for key, value in notes.items()),
    )
    test.assertEqual(
        failed and tier == "kernel-checked",
        False,
        f"{item.get('id')} is certified while failing {failed}",
    )

    if recorded == "kernel-checked":
        evidence = metadata.get("ci_evidence") or {}
        test.assertEqual(evidence.get("conclusion"), "success")
        test.assertRegex(
            str(evidence.get("run")),
            RUN_URL,
            "a certified item must cite a full run URL, not a bare id",
        )
