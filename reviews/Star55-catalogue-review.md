# ✱55 source catalogue review

The seventy-eight items are checked against Project Gutenberg 78050 on printed
pages 385–394 (scan leaves 407–416). Each source ID resolves uniquely to an
existing Lean declaration. Catalogue 01 was strictly audited: its five typed
definitions/equations preserve the ordinal-couple semantics and contain no
pass-through parameters. Those five are `awaiting-ci`; later catalogues remain
`prepared`.

Catalogue 02 was likewise audited strictly. Its five statements exactly cover
right-constructor uniqueness, section characterization, incidence,
inhabitedness, and converse; none is a pass-through. They are `awaiting-ci`,
with ·121's direct Lean edge recorded to ·12.

The current PM parser accepts 1 formulas. The remaining 77 use historical
relation-valued operators, incomplete symbols, scoped matrices, or notation
outside the current grammar and therefore carry `reviewed-gap`.
