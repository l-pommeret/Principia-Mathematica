# PM II ✱104 Q427 strict semantic audit

This item-level audit is limited to the five formulas already catalogued in
`PM2-star-104-Q427.json`.  It compares the displayed first-edition statements
against the theorem types, not merely their shared proposition numbers.

Only ✱104·12 passes.  In the source, membership of β in the first ascending
cardinal of α and membership of γ in the first ascending cardinal of β imply
membership of γ in the second ascending cardinal of α.  In the typed kernel,
`Asc s t`, `Asc t u`, and `Asc2 s u` express exactly those successive
equinumerosity/type-ascent relations, and `equiv_trans` proves the stated
conclusion without an added premise or omitted direction.  It is therefore
marked `awaiting-ci`.

The other four candidates are refused:

- ✱104·01 defines `N¹cʻα` by an intersection.  The namesake Lean theorem is
  only `Asc s t ↔ EquivSet s t` by reflexivity.
- ✱104·02 defines `N¹C` as the domain of `N¹c`.  Its namesake Lean theorem
  repeats the same existential equality on both sides.
- ✱104·03 defines the lifted cardinal `μ⁽¹⁾` as an image/intersection.
  Its namesake Lean theorem is another self-equivalence and supplies neither
  operation.
- ✱104·2 asserts that the singleton image `ιʻʻα` belongs to the ascending
  cardinal of `α`.  The Lean namesake instead proves the much weaker generic
  inclusion `s ⊆ f⁻¹(image f s)` and never establishes cardinal-class membership.

The refusals are recorded in `PM2-star-104-Q427-refused.json`; no neighbouring
architecture theorem is used as a substitute target.
