import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_elementary_formation_toy",
    ROOT / "scripts/verify_elementary_formation_toy.py")
formation = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(formation)


class ElementaryFormationToyPolicyTests(unittest.TestCase):
    def test_architecture_guard_accepts_repository(self):
        formation.main()

    def test_generic_disjunction_constructor_is_rejected(self):
        source = formation.TOY.read_text(encoding="utf-8")
        mutated = source.replace(
            "  | star_1_7 (hp : Formation p) : Formation (∼ₚ p)",
            "  | disj (hp : Formation p) (hq : Formation q) : Formation (p ∨ₚ q)\n"
            "  | star_1_7 (hp : Formation p) : Formation (∼ₚ p)")
        with self.assertRaisesRegex(ValueError, "unexpected Formation constructors"):
            formation.audit(mutated)

    def test_dead_formation_result_is_rejected(self):
        source = formation.TOY.read_text(encoding="utf-8")
        mutated = source.replace(
            "formation := Formation.star_1_7 joined",
            "formation := hφ.formation")
        with self.assertRaisesRegex(ValueError, "incomplete elementary-formation toy"):
            formation.audit(mutated)


if __name__ == "__main__":
    unittest.main()
