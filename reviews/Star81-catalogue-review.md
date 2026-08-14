# ✱81 source catalogue review

The 18 loci are checked against Project Gutenberg 78050 on printed pages
519–523 (scan leaves 541–545). Every source ID resolves uniquely to an existing Lean declaration and remains `prepared` pending item-level semantic promotion.

The current parser accepts 1 formulas; 17 historical selection formulas carry `reviewed-gap`.

## Strict semantic audit of the opening five

Only ✱81·13 is promoted: its Lean statement is exactly the displayed
pointwise characterization of a selection relation. ✱81·1 proves uniqueness from
equal domains rather than the printed inclusion in `1→1`; ·11 does not retain the
printed explicit ambient-relation conjunct in its conclusion; ·12 states a domain
formula for `canonical`, not the printed fibre-value identity; and ·14 formalizes
only the first equality of the printed three-term chain. Those four remain
`prepared` pending exact replacement declarations.

## Strict semantic audit of catalogue-02

Only ✱81·2 is exact: under the displayed many-one and selection hypotheses,
the kernel proves `DʻR = DʻS ↔ R = S`, using ✱81·1 in the forward direction
and domain congruence in reverse. ✱81·15 retains an extra `y∈κ` conjunct in
its fibre equality and omits the displayed hypotheses; ·21 is tautological rather
than one-one/similarity; ·211 assumes its conclusion; ·212 constructs a selection
but does not state the required membership/domain equality. These four remain prepared.

## Strict semantic audit of catalogue-03

No item is promotable. ✱81·22 is only reflexivity of `SelectorDomain`, not the
displayed equality characterizing all possible domains. ✱81·221 proves recovery
of one selection from its domain, not equality between the whole selection class
and the image of the domain class. ✱81·23 is a reflexive equality that never uses
the selection, many-one, or membership hypotheses and does not compare the two
printed fibres. ✱81·24 and ·25 likewise return reflexive set equalities after
discarding their hypotheses instead of proving membership in the required
smaller/larger selection-domain classes. All five therefore remain `prepared`.

## Strict semantic audit of catalogue-04

✱81·3 and ·31 are exact in the closing extensional kernel. `FibreFamily P K`
is the typed reconstruction of the indexed fibre class `P→ʻʻκ`, while
`RepresentativeDomains` is definitionally the displayed class of subclasses
meeting every fibre uniquely. Thus ·3 is its exact characterization, and ·31
is invariance of that class under equality of fibre families. Neither proof calls
an earlier PM theorem. ✱81·26 is not exact: its conclusion repeats
`SelectorDomain p k μ` on both sides and discards the required removal-of-fibre
equivalence, so it remains `prepared`.
