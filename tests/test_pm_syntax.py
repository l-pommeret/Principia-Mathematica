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

    def test_equal_group_one_disjunction_marks_preserve_left_association(self):
        parsed = shape("p . ∨ . q . ∨ . r")
        self.assertEqual(parsed["tag"], "or")
        self.assertEqual(parsed["children"][0]["tag"], "or")
        self.assertEqual(parsed["children"][1]["value"], "r")

    def test_star_3_12_printed_marks_are_left_associated(self):
        parsed = statement_shape(
            "✱3·12.  ⊢ : ∼p . ∨ . ∼q . ∨ . p . q "
            "[✱2·11 (∼p ∨ ∼q)/p]"
        )
        asserted = parsed["children"][0]
        self.assertEqual(asserted["tag"], "or")
        self.assertEqual(asserted["children"][0]["tag"], "or")
        self.assertEqual(asserted["children"][1]["tag"], "and")

    def test_star_3_2_printed_marks_are_right_nested_implications(self):
        parsed = statement_shape(
            "✱3·2.  ⊢ : p . ⊃ : q . ⊃ . p . q [✱3·12]"
        )
        asserted = parsed["children"][0]
        self.assertEqual(asserted["tag"], "implies")
        self.assertEqual(asserted["children"][0]["value"], "p")
        self.assertEqual(asserted["children"][1]["tag"], "implies")
        self.assertEqual(asserted["children"][1]["children"][0]["value"], "q")
        self.assertEqual(asserted["children"][1]["children"][1]["tag"], "and")

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

    def test_q400_descriptive_function_stroke_is_an_of_application(self):
        parsed = statement_shape("✱100·2. ⊢ . E!Ncʻα [✱32·12.(✱100·01)]")
        self.assertEqual(parsed, {
            "tag": "assert",
            "children": [{
                "tag": "exists_value",
                "children": [{
                    "tag": "of",
                    "children": [
                        {"tag": "atom", "value": "Nc"},
                        {"tag": "class_reference", "value": "α"},
                    ],
                }],
            }],
        })

    def test_q400_of_stroke_cannot_be_mutated_into_an_identifier(self):
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "PM `of` application"):
            statement_shape("✱100·2. ⊢ . E!Ncα [✱32·12.(✱100·01)]")

    def test_q100_51_seals_a_class_value_on_the_left_of_membership(self):
        parsed = statement_shape("✱100·51. ⊢ : μ ∈ NC . α ∈ μ .⊃ . smʻʻμ = Ncʻα")
        antecedent = parsed["children"][0]["children"][0]
        membership = antecedent["children"][1]
        self.assertEqual(membership["children"][0]["tag"], "class_reference")

    def test_q101_16_preserves_the_printed_alpha_subscript_on_implication(self):
        parsed = statement_shape("✱101·16. ⊢ :. μ ∈ NC − ιʻ0 .⊃ : α ∈ μ .⊃ₐ. ∃!α")
        self.assertIn("formal_implies", tags(parsed))

    def test_q101_16_binary_class_difference_is_not_a_prefix_complement(self):
        parsed = statement_shape("✱101·16. ⊢ . μ ∈ NC − ιʻ0")
        self.assertIn("class_difference", tags(parsed))
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "unconsumed token"):
            statement_shape("✱101·16. ⊢ . μ ∈ NC ιʻ0")

    def test_q101_24_uses_class_context_for_one_and_cl_value(self):
        parsed = statement_shape("✱101·24. ⊢ : ∃!α .⊃ . ∃!1 ∩ Clʻα")
        self.assertIn("class_intersection_spec", tags(parsed))
        self.assertIn("class_constant_reference", tags(parsed))

    def test_q101_25_preserves_object_level_not_equal(self):
        parsed = statement_shape("✱101·25. ⊢ : α ∈ 1 . β ⊂ α . β ≠ α .⊃ . β ∈ 0")
        self.assertIn("not_equal", tags(parsed))
        self.assertNotIn("not", tags(parsed))

    def test_q101_301_preserves_the_alpha_hat_class_binder(self):
        parsed = statement_shape("✱101·301. ⊢ . 2 = α̂{(∃x). x ∈ α . α − ιʻx ∈ 1}")
        self.assertIn("class_comprehension_spec", tags(parsed))

    def test_q102_01_preserves_explicit_type_indices(self):
        parsed = statement_shape("✱102·01. NCᵝ(α) = DʻNc(αᵦ) Df")
        self.assertIn("type_indexed", tags(parsed))
        self.assertIn("apply_named", tags(parsed))

    def test_q102_11_and_13_preserve_relation_type_indices(self):
        binary = statement_shape("✱102·11. ⊢ : R ∈ 1→1 .⊃ . R₍ₓ,ᵧ₎ ∈ 1(x)→1(y)")
        unary = statement_shape("✱102·13. ⊢ : R ∈ 1→1 .⊃ . Rₓ ∈ 1(x)→1")
        self.assertIn("relation_type_indexed", tags(binary))
        self.assertIn("relation_type_indexed", tags(unary))

    def test_q102_2_preserves_the_indexed_similarity_relation(self):
        parsed = statement_shape("✱102·2. ⊢ : γ sm₍ₐ,ᵦ₎ δ .≡ . γ sm δ . γ ∈ tʻα . δ ∈ tʻβ")
        similarities = [
            child for child in parsed["children"][0]["children"]
            if child["tag"] == "similar"
        ]
        self.assertEqual(similarities[0]["value"], "₍ₐ,ᵦ₎")

    def test_nested_of_application_preserves_left_nesting(self):
        parsed = shape("E!Ncʻα")
        value = parsed["children"][0]
        self.assertEqual(value["tag"], "of")
        self.assertEqual(value["children"][0]["value"], "Nc")

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

    def test_star_10_02_preserves_formal_implication_subscript(self):
        parsed = statement_shape("✱10·02. φx ⊃ₓ ψx .=. (x).φx ⊃ ψx  Df")
        self.assertEqual(parsed["tag"], "definition")
        self.assertEqual(parsed["children"][0]["tag"], "formal_implies")
        self.assertEqual(parsed["children"][0]["value"], "ₓ")

    def test_double_assertion_scope_marks_are_not_object_connectives(self):
        parsed = statement_shape("✱5·42. ⊢ : :p . ⊃ . q")
        self.assertEqual(parsed["tag"], "assert")
        self.assertEqual(parsed["children"][0]["tag"], "implies")

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
        self.assertEqual(membership["children"][1]["tag"], "class_comprehension_spec")
        self.assertEqual(contextual["tag"], "class_scope")
        self.assertIn("class_bound", tags(contextual))
        self.assertNotIn("class_incomplete", tags(membership))
        self.assertNotIn("class_incomplete", tags(contextual))

    def test_class_equality_is_contextual_not_native_set_equality(self):
        defined = shape("α = ẑ(φz)")
        extensional = shape("ẑ(φz) = ẑ(ψz)")
        self.assertEqual(defined["tag"], "class_extensional_equal")
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
        self.assertEqual(defined["tag"], "relation_extensional_equal")
        self.assertNotIn("relation_incomplete", tags(contextual))

    def test_incomplete_class_or_relation_cannot_escape_without_context(self):
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "without an explicit context"):
            shape("ẑ(φz)")
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "without an explicit context"):
            shape("x̂ŷφ(x,y)")

    def test_class_algebra_is_sealed_inside_its_context(self):
        intersection = shape("x ∈ α ∩ β")
        union = shape("x ∈ α ∪ β")
        complement = shape("x ∈ −α")
        inclusion = shape("α ⊂ β")
        contextual = shape("f{α ∪ β}")
        self.assertIn("class_intersection_spec", tags(intersection))
        self.assertIn("class_union_spec", tags(union))
        self.assertIn("class_complement_spec", tags(complement))
        self.assertEqual(inclusion["tag"], "class_inclusion")
        self.assertEqual(contextual["tag"], "class_scope")
        for parsed in (intersection, union, complement, inclusion, contextual):
            self.assertFalse(any(tag in {
                "class_symbol", "class_union", "class_intersection", "class_complement"
            } for tag in tags(parsed)))

    def test_freestanding_class_algebra_is_rejected(self):
        for source in ("α", "α ∩ β", "−α"):
            with self.subTest(source=source):
                with self.assertRaisesRegex(
                    pm_syntax.PMSyntaxError, "without an explicit context"
                ):
                    shape(source)

    def test_relation_algebra_is_sealed_inside_propositions(self):
        membership = shape("R ∈ Rel")
        intersection = shape("R ∩̇ S = S ∩̇ R")
        union = shape("R ⋃̇ S = S ⋃̇ R")
        complement = shape("−̇R = −̇S")
        inclusion = shape("R ⊂̇ S")
        relative = shape("(R | S) | P = R | (S | P)")
        square = shape("R² = R | R")
        converse = shape("Ř = x̂ŷyRx")
        self.assertEqual(membership["tag"], "relation_membership")
        self.assertIn("relation_intersection_spec", tags(intersection))
        self.assertIn("relation_union_spec", tags(union))
        self.assertIn("relation_complement_spec", tags(complement))
        self.assertEqual(inclusion["tag"], "relation_inclusion")
        self.assertIn("relative_product_spec", tags(relative))
        self.assertIn("relation_power_spec", tags(square))
        self.assertIn("relation_converse_spec", tags(converse))
        for parsed in (membership, intersection, union, complement, inclusion,
                       relative, square, converse):
            self.assertFalse(any(tag in {
                "relation_symbol", "relation_union", "relation_intersection",
                "relation_complement", "relative_product", "relation_converse",
                "relation_power", "relation_incomplete",
            } for tag in tags(parsed)))

    def test_freestanding_relation_algebra_is_rejected(self):
        for source in ("R", "R ∩̇ S", "R | S", "Ř", "R²"):
            with self.subTest(source=source):
                with self.assertRaisesRegex(
                    pm_syntax.PMSyntaxError, "without an explicit context"
                ):
                    shape(source)


if __name__ == "__main__":
    unittest.main()
