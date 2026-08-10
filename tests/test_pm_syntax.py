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


def tags(node):
    return [node["tag"]] + [tag for child in node.get("children", []) for tag in tags(child)]


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
            "children": [{
                "tag": "apply_general", "value": "φ",
                "children": [{"tag": "atom", "value": "x"}],
            }],
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

    def test_general_and_predicative_applications_are_distinct(self):
        general = shape("φx")
        predicative = shape("φ!x")
        binary = shape("ψ(x,y)")
        self.assertEqual(general["tag"], "apply_general")
        self.assertEqual(predicative["tag"], "apply_predicative")
        self.assertNotEqual(general, predicative)
        self.assertEqual([child["value"] for child in binary["children"]], ["x", "y"])

    def test_star_12_1_preserves_function_quantifier_and_bang(self):
        parsed = statement_shape("✱12·1. ⊢ : (∃f) : φx . ≡ₓ . f!x    Pp")
        existential = parsed["children"][0]
        self.assertEqual(existential["tag"], "exists")
        self.assertEqual(existential["value"], "f")
        equivalence = existential["children"][0]
        self.assertEqual(equivalence["tag"], "formal_equiv")
        self.assertEqual(equivalence["value"], "ₓ")
        self.assertEqual(equivalence["children"][0]["tag"], "apply_general")
        self.assertEqual(equivalence["children"][1]["tag"], "apply_predicative")

    def test_trailing_proof_reference_is_not_object_syntax(self):
        parsed = statement_shape(
            "✱2·45. ⊢ : ∼(p ∨ q) . ⊃ . ∼p [✱2·2.Transp.]"
        )
        self.assertEqual(parsed["tag"], "assert")
        self.assertEqual(parsed["children"][0]["tag"], "implies")

    def test_star_13_01_binds_one_predicative_function(self):
        parsed = statement_shape(
            "✱13·01. x = y .=: (φ) : φ!x .⊃. φ!y  Df"
        )
        self.assertEqual(parsed["tag"], "definition")
        self.assertEqual(parsed["children"][0]["tag"], "equal")
        quantified = parsed["children"][1]
        self.assertEqual((quantified["tag"], quantified["value"]), ("forall", "φ"))
        implication = quantified["children"][0]
        self.assertEqual(implication["tag"], "implies")
        self.assertEqual(
            [child["tag"] for child in implication["children"]],
            ["apply_predicative", "apply_predicative"],
        )
        self.assertEqual(
            [child["value"] for child in implication["children"]], ["φ", "φ"]
        )

    def test_description_scope_is_contextual_not_a_term_application(self):
        narrow = shape("[(℩x)(φx)] . ψ(℩x)(φx) .⊃. p")
        wide = shape("[(℩x)(φx)] : ψ(℩x)(φx) .⊃. p")
        self.assertEqual(narrow["tag"], "implies")
        self.assertEqual(narrow["children"][0]["tag"], "description_scope")
        self.assertEqual(wide["tag"], "description_scope")
        self.assertEqual(wide["children"][1]["tag"], "implies")
        self.assertNotEqual(narrow, wide)
        self.assertNotIn("description", tags(narrow))
        self.assertNotIn("description", tags(wide))
        self.assertIn("description_bound", tags(narrow))

    def test_star_14_01_definition_has_contextual_description_lhs(self):
        parsed = statement_shape(
            "✱14·01. [(℩x)(φx)] . ψ(℩x)(φx) .=: "
            "(∃b) : φx .≡ₓ. x = b : ψb  Df"
        )
        self.assertEqual(parsed["tag"], "definition")
        self.assertEqual(parsed["children"][0]["tag"], "description_scope")
        self.assertEqual(parsed["children"][1]["tag"], "exists")
        self.assertNotIn("description", tags(parsed))

    def test_class_abstraction_is_eliminated_in_membership_and_application(self):
        membership = shape("x ∈ ẑ(φz)")
        contextual = shape("f{ẑ(φz)}")
        self.assertEqual(membership["tag"], "class_membership")
        self.assertEqual(membership["value"], "z")
        self.assertEqual(contextual["tag"], "class_scope")
        self.assertIn("class_bound", tags(contextual))
        self.assertNotIn("class_incomplete", tags(membership))
        self.assertNotIn("class_incomplete", tags(contextual))

    def test_class_equality_is_contextual_not_native_set_equality(self):
        defined = shape("α = ẑ(φz)")
        extensional = shape("ẑ(φz) = ẑ(ψz)")
        self.assertEqual(defined["tag"], "class_defined_equal")
        self.assertEqual(extensional["tag"], "class_extensional_equal")
        self.assertNotIn("class_incomplete", tags(extensional))

    def test_relation_application_and_incomplete_relation_context(self):
        value = shape("xRy")
        contextual = shape("f{x̂ŷφ(x,y)}")
        defined = shape("R = x̂ŷφ(x,y)")
        self.assertEqual(value, {
            "tag": "relation_value", "value": "R",
            "children": [{"tag": "atom", "value": "x"},
                         {"tag": "atom", "value": "y"}],
        })
        self.assertEqual(contextual["tag"], "relation_scope")
        self.assertIn("relation_bound", tags(contextual))
        self.assertEqual(defined["tag"], "relation_defined_equal")
        self.assertNotIn("relation_incomplete", tags(contextual))

    def test_incomplete_class_or_relation_cannot_escape_without_context(self):
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "without an explicit context"):
            shape("ẑ(φz)")
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "without an explicit context"):
            shape("x̂ŷφ(x,y)")


if __name__ == "__main__":
    unittest.main()
