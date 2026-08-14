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

Catalogue 03 strict audit accepts only ·15 and ·2 as exact (`awaiting-ci`).
Items ·16, ·161, and ·17 remain `prepared`: their Lean statements restrict
`R` to a relation already witnessed as an ordinal couple, while the printed
domain/converse-domain characterizations quantify without that extra witness.
This is a substantive weakening, so those three are explicitly refused.

Catalogue 04 accepts ·201, ·21, ·22, and ·221 as exact (`awaiting-ci`).
Item ·202 remains `prepared`: Lean proves equality of couples equivalent to
equality of both components, but omits the printed chained equivalence with
the equality of the reversed couples. The missing biconditional is substantive.

The current PM parser accepts 1 formulas. The remaining 77 use historical
relation-valued operators, incomplete symbols, scoped matrices, or notation
outside the current grammar and therefore carry `reviewed-gap`.
