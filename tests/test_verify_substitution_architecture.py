import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class SubstitutionArchitectureTests(unittest.TestCase):
    def test_static_architecture_contract(self):
        source = (ROOT / "Principia/Deduction/System.lean").read_text()
        self.assertIn("inductive Derivation", source)
        empty = source.index("| star_1_1 {p q : Elementary []}")
        nonempty = source.index("| star_1_11 {\u0393 : RealContext}")
        schema = source.index("theorem instantiateSchema")
        self.assertLess(empty, nonempty)
        self.assertLess(nonempty, schema)
        self.assertIn("Derivation p → Derivation (p ⊃ₚ q) → Derivation q", source[empty:nonempty])
        self.assertIn("(hasRealVariable : Γ ≠ [])", source[nonempty:schema])
        self.assertIn("induction proof with", source[schema:])


if __name__ == "__main__":
    unittest.main()
