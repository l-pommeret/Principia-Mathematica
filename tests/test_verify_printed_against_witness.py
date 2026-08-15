"""Regression tests for the PM-VERBATIM/Gutenberg witness gate."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_printed_against_witness as gate


PROPOSITION = "PM1:✱4·57"
WITNESS_READING = (
    r"\(\vdash: {\sim}({\sim}p.{\sim}q).\equiv .p\lor q "
    r"\quad[\text{*4·56·12}]\)"
)
ALTERED_READING = "✱4·57. ⊢ : ∼(∼q ∨ q) . ≡ . p ∨ q [✱4·56·12]"


class PrintedWitnessGateTests(unittest.TestCase):
    def make_repository(
        self,
        root: Path,
        *,
        local_reading: str = ALTERED_READING,
        exemptions: list[dict[str, str]] | None = None,
    ) -> None:
        lean = root / "Principia" / "Example.lean"
        lean.parent.mkdir(parents=True)
        lean.write_text(
            "\n".join(
                (
                    f"/- PM-VERBATIM-BEGIN {PROPOSITION}",
                    local_reading,
                    f"PM-VERBATIM-END {PROPOSITION} -/",
                    "",
                )
            ),
            encoding="utf-8",
        )
        witness = root / "metadata" / "witness.txt"
        witness.parent.mkdir(parents=True)
        witness.write_text(f"*4·57. {WITNESS_READING}\n", encoding="utf-8")
        registry = root / "metadata" / "printed_witness_exemptions.json"
        registry.write_text(
            json.dumps(
                {"schema_version": 1, "exemptions": exemptions or []},
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def verify(self, root: Path) -> gate.Report:
        return gate.verify(
            root,
            witnesses={"PM1": Path("metadata/witness.txt")},
        )

    def test_deliberately_altered_block_is_detected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_repository(root)
            report = self.verify(root)

        self.assertEqual(1, report.compared)
        self.assertEqual([PROPOSITION], [item.block.proposition for item in report.divergences])
        self.assertEqual(0, report.conforming)

    def test_exact_exemption_with_written_justification_passes(self) -> None:
        exemption = {
            "proposition": PROPOSITION,
            "gutenberg_reading": WITNESS_READING,
            "repository_reading": gate._local_statement(
                gate.Block(PROPOSITION, ALTERED_READING, Path("Example.lean"), 1)
            ),
            "reason": (
                "Le fac-similé de la page montre nettement que Gutenberg a "
                "interverti les variables de cette formule imprimée."
            ),
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_repository(root, exemptions=[exemption])
            report = self.verify(root)

        self.assertEqual(1, report.compared)
        self.assertEqual(1, report.exempted)
        self.assertEqual([], report.divergences)
        self.assertEqual([], report.registry_errors)

    def test_exemption_without_a_substantive_reason_is_refused(self) -> None:
        exemption = {
            "proposition": PROPOSITION,
            "gutenberg_reading": WITNESS_READING,
            "repository_reading": ALTERED_READING,
            "reason": "",
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.make_repository(root, exemptions=[exemption])
            registry = root / "metadata" / "printed_witness_exemptions.json"
            with self.assertRaisesRegex(gate.RegistryError, "champ vide"):
                gate.load_exemptions(registry)


if __name__ == "__main__":
    unittest.main()
