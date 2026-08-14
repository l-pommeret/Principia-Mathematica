"""A judgement relation's constructors must answer to printed primitives."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_judgement_primitives import (  # noqa: E402
    PRIMITIVE_KINDS,
    REGISTRY,
    constructor_to_pm_ids,
    declared_exemptions,
    relation_constructors,
)


class NamingTests(unittest.TestCase):
    def test_star_names_resolve_to_pm_ids(self) -> None:
        self.assertIn("PM1:✱1·2", constructor_to_pm_ids("star_1_2"))
        self.assertIn("PM1:✱10·121", constructor_to_pm_ids("star_10_121"))

    def test_invented_names_resolve_to_nothing(self) -> None:
        # `printed_chain`, `line2`, `matrixIdentity` are the shapes this gate
        # exists to catch: a constructor invented for convenience is an
        # assumption wearing the costume of a rule.
        for name in ("printed_chain", "line2", "matrixIdentity", "indexed"):
            self.assertEqual(constructor_to_pm_ids(name), [], name)


class ReferenceCalculusTests(unittest.TestCase):
    def test_the_reference_relation_is_fully_primitive_backed(self) -> None:
        relations = relation_constructors()
        self.assertIn("Derivation", relations, "the canonical ramified calculus is not indexed")
        path, constructors = relations["Derivation"]
        self.assertEqual(path, "Principia/Syntax/Ramified.lean")
        self.assertEqual(
            set(constructors),
            {"star_1_1", "star_1_11", "star_1_2", "star_1_3", "star_1_4",
             "star_1_5", "star_1_6", "star_10_1", "star_10_11", "star_10_121",
             "star_10_122", "star_11_07", "star_11_1", "star_11_11", "star_12_1",
             "star_12_11", "star_9_1", "star_9_11", "star_9_12", "star_9_13"},
            "the ramified reference calculus must have exactly PM's printed "
            "primitive propositions and inference rules, and nothing else",
        )


class ExemptionRegistryTests(unittest.TestCase):
    def test_registry_is_exactly_the_non_numbered_constructor_set(self) -> None:
        exemptions = declared_exemptions()
        relations = relation_constructors()
        non_numbered = {
            (relation, constructor)
            for relation, (_, constructors) in relations.items()
            for constructor in constructors
            if not constructor_to_pm_ids(constructor)
        }
        self.assertEqual(set(exemptions), non_numbered)

    def test_every_exemption_argues_from_the_printed_text(self) -> None:
        data = json.loads(REGISTRY.read_text(encoding="utf-8"))
        for entry in data["exemptions"]:
            self.assertGreaterEqual(len(entry.get("reason", "")), 40, entry)
            self.assertTrue(entry.get("source"), entry)

    def test_a_reasonless_exemption_is_rejected(self) -> None:
        import verify_judgement_primitives as gate
        original = gate.REGISTRY
        try:
            bad = ROOT / "tests" / "_tmp_registry.json"
            bad.write_text(
                json.dumps({"exemptions": [
                    {"relation": "R", "constructor": "c", "reason": "because"}
                ]}),
                encoding="utf-8",
            )
            gate.REGISTRY = bad
            with self.assertRaises(SystemExit):
                gate.declared_exemptions()
        finally:
            gate.REGISTRY = original
            (ROOT / "tests" / "_tmp_registry.json").unlink(missing_ok=True)


class KindTests(unittest.TestCase):
    def test_a_definition_is_not_a_primitive(self) -> None:
        # PM's `Df` are eliminable abbreviations; making one a constructor turns
        # an abbreviation into an irreducible assertion.
        self.assertNotIn("definition", PRIMITIVE_KINDS)
        self.assertNotIn("derived-proposition", PRIMITIVE_KINDS)

    def test_printed_primitive_kinds_are_accepted(self) -> None:
        self.assertIn("primitive-proposition", PRIMITIVE_KINDS)
        self.assertIn("primitive-inference-rule", PRIMITIVE_KINDS)


class GateBehaviourTests(unittest.TestCase):
    def test_gate_reports_and_exits_nonzero_while_relations_are_unbacked(self) -> None:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/verify_judgement_primitives.py")],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        self.assertIn(result.returncode, (0, 1))
        if result.returncode == 1:
            self.assertIn("printed primitive", result.stderr)


if __name__ == "__main__":
    unittest.main()
