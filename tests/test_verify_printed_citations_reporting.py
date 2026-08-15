"""Regression tests for non-vacuous printed-citation reporting."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_printed_citations as citations  # noqa: E402


class PrintedCitationReportingTests(unittest.TestCase):
    def _run_main(self) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with (
            mock.patch.object(sys, "argv", ["verify_printed_citations.py"]),
            contextlib.redirect_stdout(stdout),
            contextlib.redirect_stderr(stderr),
        ):
            return citations.main(), stdout.getvalue(), stderr.getvalue()

    def test_empty_or_entirely_uncited_corpus_cannot_report_success(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            items = Path(directory)
            with mock.patch.object(citations, "ITEMS", items):
                code, stdout, stderr = self._run_main()

            self.assertEqual(code, 1)
            self.assertEqual(stdout, "")
            self.assertIn("0 proofs were audited", stderr)
            self.assertIn("0 of 0 audited proofs", stderr)
            self.assertNotIn("printed citations verified", stderr)

            (items / "uncited.json").write_text(
                json.dumps(
                    {
                        "items": [
                            {
                                "id": "PM1:✱2·01",
                                "formal_status": "kernel-checked",
                                "declaration": "PM.Test.star_2_01",
                                "printed_dependencies": [],
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(citations, "ITEMS", items),
                mock.patch.object(
                    citations,
                    "print_terms",
                    return_value={"PM.Test.star_2_01": "theorem PM.Test.star_2_01"},
                ),
            ):
                code, stdout, stderr = self._run_main()

            self.assertEqual(code, 1)
            self.assertEqual(stdout, "")
            self.assertIn("none of the 1 audited proofs", stderr)
            self.assertIn("1 of 1 audited proofs", stderr)
            self.assertNotIn("printed citations verified", stderr)

    def test_success_uses_the_real_audit_counters(self) -> None:
        stats = {
            "audited": 3,
            "follows-the-print": 2,
            "more-explicit-than-print": 1,
            "no-citations-recorded": 1,
        }
        with mock.patch.object(citations, "audit", return_value=([], stats)):
            code, stdout, stderr = self._run_main()

        self.assertEqual(code, 0)
        self.assertEqual(stderr, "")
        self.assertIn("2 of 3 audited proofs follow", stdout)
        self.assertIn("1 are more explicit than print", stdout)
        self.assertIn("1 of 3 audited proofs have no checkable", stdout)


if __name__ == "__main__":
    unittest.main()
