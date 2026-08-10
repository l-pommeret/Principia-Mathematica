import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import pm_syntax


def shape(source: str):
    return pm_syntax.parse(source).to_dict()


def statement_shape(source: str):
    return pm_syntax.parse_statement(source).to_dict()


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

    def test_group_two_binder_stops_before_equal_group_one(self):
        parsed = shape("(x).φx . ⊃ . p")
        self.assertEqual(parsed["tag"], "implies")
        self.assertEqual(parsed["children"][0], {
            "tag": "forall", "value": "x",
            "children": [{"tag": "atom", "value": "φx"}],
        })

    def test_group_two_binder_contains_equal_group_three_product(self):
        parsed = shape("(x).φx . ψx")
        self.assertEqual(parsed["tag"], "forall")
        self.assertEqual(parsed["children"][0]["tag"], "and")

    def test_disjunction_definition_scope_pair(self):
        left = shape("(x).φx . ∨ . p")
        right = shape("(x).φx ∨ p")
        self.assertEqual(left["tag"], "or")
        self.assertEqual(left["children"][0]["tag"], "forall")
        self.assertEqual(right["tag"], "forall")
        self.assertEqual(right["children"][0]["tag"], "or")

    def test_existential_and_multiple_variable_binders(self):
        existential = shape("(∃x).φx")
        multiple = shape("(x, y):φxy")
        self.assertEqual(existential["tag"], "exists")
        self.assertEqual(existential["value"], "x")
        self.assertEqual(multiple["tag"], "forall")
        self.assertEqual(multiple["value"], "x,y")

    def test_numbered_disjunction_definition(self):
        parsed = statement_shape("✱9·03. (x).φx.∨.p :=. (x).φx∨p  Df")
        self.assertEqual(parsed["tag"], "definition")
        self.assertEqual(parsed["children"][0]["tag"], "or")
        self.assertEqual(parsed["children"][1]["tag"], "forall")

    def test_star_2_33_records_left_association(self):
        parsed = statement_shape("✱2·33. p ∨ q ∨ r .=. (p ∨ q) ∨ r Df")
        self.assertEqual(parsed["tag"], "definition")
        self.assertEqual(parsed["children"][0], parsed["children"][1])

    def test_unmarked_implication_remains_right_associated(self):
        parsed = shape("p ⊃ q ⊃ r")
        self.assertEqual(parsed["tag"], "implies")
        self.assertEqual(parsed["children"][1]["tag"], "implies")


if __name__ == "__main__":
    unittest.main()
