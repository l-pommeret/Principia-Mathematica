# ✱35 catalogues 03–04 strict semantic audit

These two audits cover exactly five formulas each.  All ten theorem types
preserve the complete printed equalities, so no refusal split is required.

Catalogue 03 treats intersection of restricted relations.  The pointwise
definitions of left restriction, right restriction, simultaneous restriction,
class intersection, and relation intersection make ✱35·12–·15 exact
extensional translations.  The Lean theorem for ·16 returns a conjunction of
the two equalities in PM's printed equality chain; neither equality is dropped.

Catalogue 04 continues the same pattern.  The Lean theorems for ·17 and ·18
again retain both equalities in their respective chains.  For ·22 and ·23,
the existential middle term in `composition` is unchanged when the endpoint
restriction moves across composition, matching the printed orientation.
Finally, ·24 is explicitly a definition in PM and is represented by the
definitional equality between `leftRestrictedComposition` and the bracketed
composition.  No theorem is strengthened, weakened, or direction-reversed.

All ten items are promoted in place to `awaiting-ci`; their existing
`reviewed-gap` parser status is independent of this semantic verdict.
