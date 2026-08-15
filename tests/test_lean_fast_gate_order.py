"""Regression test for the trust boundary at the start of Lean fast CI."""

from __future__ import annotations

import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-fast.yml"


def workflow_step_blocks() -> list[list[str]]:
    """Return the top-level step blocks from the workflow's sole job."""
    lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
    starts = [index for index, line in enumerate(lines) if line.startswith("      - ")]
    return [
        lines[start : starts[position + 1] if position + 1 < len(starts) else None]
        for position, start in enumerate(starts)
    ]


class LeanFastGateOrderTests(unittest.TestCase):
    def test_gate_integrity_is_first_post_checkout_step(self) -> None:
        steps = workflow_step_blocks()

        self.assertIn("uses: actions/checkout@v5", steps[0][0])
        self.assertEqual(steps[1][0].strip(), "- name: Verify gate integrity")
        self.assertIn(
            "run: python3 scripts/verify_gate_integrity.py",
            [line.strip() for line in steps[1]],
        )


if __name__ == "__main__":
    unittest.main()
