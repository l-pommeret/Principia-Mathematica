import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import pm_syntax


def shape(source: str):
    return pm_syntax.parse(source).to_dict()


class PMDotSyntaxTests(unittest.TestCase):
    def test_colon_counts_as_two_dots(self):
        self.assertEqual(pm_syntax.mark_count(":"), 2)
        self.assertEqual(pm_syntax.mark_count(":."), 3)
        self.assertEqual(pm_syntax.mark_count("::"), 4)

    def test_printed_permutation_example(self):
        self.assertEqual(shape("p ∨ q . ⊃ . q ∨ p"), {
            "tag": "implies", "children": [
                {"tag": "or", "children": [{"tag": "atom", "value": "p"}, {"tag": "atom", "value": "q"}]},
                {"tag": "or", "children": [{"tag": "atom", "value": "q"}, {"tag": "atom", "value": "p"}]},
            ],
        })

    def test_stronger_disjunction_scope_is_outer(self):
        parsed = shape("p : ∨ : q . ⊃ . q ∨ p")
        self.assertEqual(parsed["tag"], "or")
        self.assertEqual(parsed["children"][1]["tag"], "implies")

    def test_stronger_final_disjunction_scope_is_outer(self):
        parsed = shape("p ∨ q . ⊃ . q : ∨ : p")
        self.assertEqual(parsed["tag"], "or")
        self.assertEqual(parsed["children"][0]["tag"], "implies")

    def test_group_three_product_loses_to_equal_group_one(self):
        parsed = shape("p ⊃ q . q ⊃ r . ⊃ . p ⊃ r")
        self.assertEqual(parsed["tag"], "implies")
        self.assertEqual(parsed["children"][0]["tag"], "and")

    def test_two_dot_product_is_outer(self):
        parsed = shape("p ⊃ q : q ⊃ r . ⊃ . p ⊃ r")
        self.assertEqual(parsed["tag"], "and")
        self.assertEqual(parsed["children"][1]["tag"], "implies")

    def test_assertion_scope_is_judgment_not_conjunction(self):
        parsed = shape("⊢ : p ∨ q . ⊃ . q ∨ p")
        self.assertEqual(parsed["tag"], "assert")
        self.assertEqual(parsed["children"][0]["tag"], "implies")

    def test_parentheses_and_negation(self):
        parsed = shape("∼(p ∨ q) . ⊃ . q")
        self.assertEqual(parsed["tag"], "implies")
        self.assertEqual(parsed["children"][0]["tag"], "not")


if __name__ == "__main__":
    unittest.main()
