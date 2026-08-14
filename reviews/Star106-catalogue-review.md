# ✱106 source catalogue review

The forty-seven loci are checked against Project Gutenberg 78255 on printed
pages 61–65 (scan leaves 101–105). Source IDs and Lean declarations form a
duplicate-free 47/47 bijection. The catalogue was initially recorded as
`prepared` pending semantic promotion; Catalogue 01 is promoted below.

The parser accepts 20 formulas; 27 descending-cardinal formulas carry `reviewed-gap`.

## Catalogue 01 strict semantic audit

Scope: the first five loci of ✱106 on PM II p. 61 (1912 scan leaf 101),
checked against the verbatim source blocks and their named Lean declarations.
Promotion is based on the complete typed propositions, not on matching names.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱106·01 | `star_106_01` | exact, awaiting CI | `TypedNc Nc T` unfolds pointwise to `Nc ∩ T`; instantiating `T` with PM's `tʻt₀₀ʻα` is exactly the displayed definition. |
| ✱106·011 | `star_106_011` | exact, awaiting CI | The same polymorphic definition, instantiated at the `tʻt¹¹ʻα` stratum, preserves both operands and intersection. |
| ✱106·012 | `star_106_012` | exact, awaiting CI | The `t₀₁` stratum is an explicit parameter; the theorem states exactly the corresponding `Nc ∩ T` definition, with no extra premise. |
| ✱106·02 | `star_106_02` | exact, awaiting CI | The `t¹₀` instance of the typed intersection has the same equality and direction as PM's definition. |
| ✱106·021 | `star_106_021` | exact, awaiting CI | The leading type descent is represented by the chosen `T`; Lean neither erases an operand nor assumes the defining equality. |

All five are definitional equalities proved by `rfl`. Their bodies depend only
on the local `TypedNc` and `inter` definitions, which are carrier
infrastructure rather than numbered PM propositions. Consequently the printed,
Lean-numbered, and normalized dependency graphs are all empty. The exact set is
promoted to `awaiting-ci`; no refusal manifest is needed for this five-item
lot. Kernel-checked status still requires successful immutable CI evidence.

## Catalogue 02 strict semantic audit

Scope: the next five loci on PM II p. 61 (scan leaf 101). The exact and
refused subsets are recorded in disjoint manifests.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱106·03 | `star_106_03` | exact, awaiting CI | `DomainOf F M` is definitionally `∃ i, M = F i`, exactly membership of `M` in the range `DʻF`. |
| ✱106·04 | `star_106_04` | refused | PM's `smʻʻμ` is a relational image and requires similarity between the existential source `α` and result `β`; Lean uses unary `sm b`, independent of its witness `a`. |
| ✱106·041 | `star_106_041` | refused | The same unary encoding erases the source/result relation required by `smʻʻμ`; changing the type stratum does not repair it. |
| ✱106·1 | `star_106_1` | exact, awaiting CI | Unfolding `TypedNc` yields precisely membership in both factors of PM's defining intersection. |
| ✱106·101 | `star_106_101` | exact, awaiting CI | This is the same exact pointwise intersection equivalence at the `t¹¹` stratum. |

The promoted set is exactly 3/5. The two relational-image definitions remain
`prepared` with explicit semantic-mismatch refusals and cannot contribute to
source-critical coverage. All five declaration bodies cite no numbered Lean
theorem, so their printed, Lean-numbered and normalized dependency lists are
empty. CI evidence for the exact subset remains pending.
