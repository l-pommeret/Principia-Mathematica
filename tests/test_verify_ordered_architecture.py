import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class OrderedArchitectureTests(unittest.TestCase):
    def test_static_contract(self):
        source = (ROOT / "Principia/Deduction/Ordered.lean").read_text()
        self.assertIn("structure OrderedRuleBook", source)
        self.assertIn("Primitive : OrderedFormula Γ order → Type", source)
        self.assertNotIn("inductive OrderedDerivation", source)
        self.assertNotIn("| detach", source)


if __name__ == "__main__":
    unittest.main()
