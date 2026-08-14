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
        self.assertIn("class_difference_spec", tags(parsed))
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

    def test_q600_star_250_01_preserves_relation_hat_binder(self):
        parsed = statement_shape(
            "✱250·01. Bord = P̂ (Cl exʻCʻP ⊂ ∃ʻminₚ) Df"
        )
        self.assertEqual(parsed["tag"], "relation_defined_equal")
        abstraction = parsed["children"][1]
        self.assertEqual(abstraction["tag"], "relation_comprehension_spec")
        self.assertEqual(abstraction["value"], "P")
        self.assertEqual(abstraction["children"][0]["tag"], "class_inclusion")
        self.assertNotIn("class_comprehension_spec", tags(parsed))

    def test_q600_relation_hat_cannot_escape_its_context(self):
        with self.assertRaisesRegex(
            pm_syntax.PMSyntaxError, "without an explicit context"
        ):
            shape("P̂ (Cl exʻCʻP ⊂ ∃ʻminₚ)")

    def test_q603_preserves_the_p_po_relation_index(self):
        parsed = statement_shape(
            "✱250·103. ⊢ : P ∈ Bord .≡ . Pₚₒ ∈ Bord [✱250·102 . ✱211·17]"
        )
        self.assertIn("relation_type_indexed", tags(parsed))

    def test_q603_preserves_undotted_relation_inclusion(self):
        parsed = statement_shape(
            "✱250·105. ⊢ : P ∈ Bord .⊃ . Pₚₒ ⊂ J [✱250·103·104]"
        )
        self.assertIn("relation_inclusion", tags(parsed))

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

    def test_q102_22_seals_class_operands_of_inclusion(self):
        parsed = statement_shape(
            "✱102·22. ⊢ : γ sm₍ₓ,ᵧ₎ δ .≡ . γ sm δ . γ ⊂ tʻx . δ ⊂ tʻy"
        )
        self.assertIn("class_inclusion", tags(parsed))

    def test_q102_23_seals_relations_used_as_of_arguments(self):
        parsed = statement_shape(
            "✱102·23. ⊢ : γ sm₍ₓ,ᵧ₎ δ .≡ . (∃R). R ∈ 1→1 . "
            "DʻR ⊂ tʻx . ᗡʻR ⊂ tʻy . DʻR = γ . ᗡʻR = δ"
        )
        self.assertIn("relation_reference", tags(parsed))

    def test_q102_24_keeps_one_y_as_a_named_application(self):
        parsed = statement_shape(
            "✱102·24. ⊢ : γ sm₍ₓ,ᵧ₎ δ .≡ . (∃R). R ∈ 1(x)→1(y) . "
            "DʻR = γ . ᗡʻR = δ"
        )
        self.assertGreaterEqual(tags(parsed).count("apply_named"), 2)

    def test_q102_45_preserves_alpha_subscript_as_a_type_index(self):
        parsed = statement_shape(
            "✱102·45. ⊢ : γ ∈ Nc(αᵦ)ʻδ .⊃ . γ ∈ Nc(αₐ)ʻγ"
        )
        self.assertIn("type_indexed", tags(parsed))

    def test_q102_55_preserves_alpha_and_beta_type_indices(self):
        parsed = statement_shape("✱102·55. ⊢ : Λ ∼∈ NCᵅ(β) .⊃ . NCᵝ(α) − ιʻΛ = NCᵅ(α)")
        def indexed_values(node):
            values = ([node.get("value")] if node["tag"] in {
                "type_indexed", "class_type_indexed"
            } else [])
            return values + [
                value for child in node.get("children", [])
                for value in indexed_values(child)
            ]
        indexed = indexed_values(parsed)
        self.assertIn("ᵅ", indexed)
        self.assertIn("ᵝ", indexed)
        self.assertIn("not_member", tags(parsed))

    def test_q102_6_preserves_gamma_hat_parenthesized_class_binder(self):
        parsed = statement_shape(
            "✱102·6. ⊢ . Nc(α)ʻβ = Nc(αᵦ)ʻβ = γ̂(γ sm β . γ ∈ tʻα) = Ncʻβ ∩ tʻα"
        )
        self.assertIn("class_comprehension_spec", tags(parsed))

    def test_q102_74_preserves_the_composite_typed_superscript(self):
        parsed = statement_shape("✱102·74. ⊢ . Λ ∈ NCᵗʻα(α)")
        self.assertIn("class_type_indexed", tags(parsed))

    def test_q102_75_seals_typed_named_classes_only_in_union_context(self):
        parsed = statement_shape("✱102·75. ⊢ . NCᵗʻα(α) = NCᵅ(α) ∪ ιʻΛ")
        self.assertIn("class_named_application", tags(parsed))

    def test_q102_86_preserves_diplomatic_xi_similarity_index(self):
        parsed = statement_shape(
            "✱102·86. ⊢ : μ = Nc(α)ʻδ . ∃!μ .⊃ . smᵟʻʻμ = Nc(ξ)ʻδ"
        )
        self.assertIn("type_indexed", tags(parsed))

    def test_q104_superscript_indices_are_explicit(self):
        for statement in ("✱104·01. ⊢ . N¹c = N²c", "✱104·03. ⊢ . μ⁽¹⁾ = N¹c", "✱104·12. ⊢ . N²c = μ⁽¹⁾", "✱104·2. ⊢ . ʻʻα ∈ N¹cʻα"):
            self.assertIn("superscript_indexed", tags(statement_shape(statement)))

    def test_q104_leading_value_strokes_are_explicit_unit_classes(self):
        parsed = statement_shape("✱104·2. ⊢ . ʻʻα ∈ N¹cʻα")
        self.assertEqual(tags(parsed).count("unit_class"), 2)

    def test_q105_38_preserves_postfix_superscript_on_braced_class(self):
        parsed = statement_shape("✱105·38. ⊢ . {μ⁽¹⁾}⁽¹⁾ = μ⁽²⁾")
        self.assertGreaterEqual(tags(parsed).count("superscript_indexed"), 3)

    def test_q105_13_preserves_braced_named_class_application(self):
        parsed = statement_shape(
            "✱105·13. ⊢ . N₁cʻα = Nc(t₁ʻα)ʻα = Nc{(t₁ʻα)ₐ}ʻα"
        )
        self.assertIn("apply_named", tags(parsed))

    def test_star_14_02_accepts_description_as_existence_argument(self):
        parsed = statement_shape("✱14·02. E!(℩x)(φx) .=: (∃b) : φx .≡ₓ. x = b Df")
        self.assertIn("description_exists", tags(parsed))

    def test_star_14_03_preserves_two_printed_description_scopes(self):
        parsed = statement_shape(
            "✱14·03. [(℩x)(φx), (℩x)(ψx)] . "
            "f{(℩x)(φx), (℩x)(ψx)}"
        )
        self.assertEqual(tags(parsed).count("description_scope"), 2)
        self.assertNotIn("description", tags(parsed))

    def test_star_14_04_keeps_unbracketed_description_at_inner_scope(self):
        parsed = statement_shape(
            "✱14·04. [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)}"
        )
        self.assertEqual(tags(parsed).count("description_scope"), 2)
        self.assertNotIn("description", tags(parsed))

    def test_q102_87_preserves_nested_diplomatic_xi_similarity_index(self):
        parsed = statement_shape(
            "✱102·87. ⊢ : μ = Nc(β)ʻδ . ∃!Nc(ξ)ʻδ .⊃ . "
            "smₐʻʻμ = smₐʻʻsmᵟʻʻμ"
        )
        self.assertGreaterEqual(tags(parsed).count("type_indexed"), 2)

    def test_q103_1_preserves_postfix_alpha_type_index(self):
        parsed = statement_shape(
            "✱103·1. ⊢ . N₀cʻα = (Ncʻα)ₐ = Nc(α)ʻα = Nc(αₐ)ʻα"
        )
        self.assertIn("type_indexed", tags(parsed))
        with self.assertRaisesRegex(pm_syntax.PMSyntaxError, "expected proposition"):
            shape("ₐNcʻα")

    def test_q103_32_seals_class_difference_before_inclusion(self):
        parsed = statement_shape("✱103·32. ⊢ . NCᵝ(α) − ιʻΛ ⊂ N₀C(α)")
        self.assertIn("class_difference_spec", tags(parsed))

    def test_q103_44_preserves_the_membership_tuple(self):
        parsed = statement_shape("✱103·44. ⊢ :: μ,ν ∈ N₀C .⊃ : μ = smʻʻν .≡ . ν = smʻʻμ")
        self.assertIn("tuple", tags(parsed))

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
