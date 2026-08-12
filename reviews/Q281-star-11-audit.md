# Q281 exact Lean audit

The diplomatic record on PM I pp. 162--163 (scan leaves 184--185) gives five
binary-function propositions, ✱11·35, ✱11·36, ✱11·37, ✱11·371, and ✱11·38.
`Star11Q281Kernel.lean` preserves both argument positions explicitly by using
an arbitrary predicate `φ : α → β → Prop`; it does not collapse the statements
to a unary or closed special case.

The translations are literal: successive PM universal and existential
quantifiers become successive Lean binders; juxtaposition in ✱11·38 becomes
conjunction; implication and equivalence retain their logical meanings.
✱11·36 keeps the printed witnesses `z` and `w`.  The proofs require no
inhabitedness assumption, `Classical`, decidability, new axiom, semantic stub,
or generic rule over the repository's `Raw` syntax.  Consequently these are
unconditional kernel proofs of the complete canonical statements, not merely
target records or architecture prerequisites.

The printed citations remain recorded in the batch metadata.  They document
the historical PM derivations; Lean checks each resulting proposition
directly in its trusted kernel.

Parser audit: the coverage parser cannot yet disambiguate PM's colon-led
scope after a two-variable binder and consequently reports a bare `φ` in
✱11·35, ✱11·37, ✱11·371, and ✱11·38. In every case the diplomatic text
contains the fully applied `φ(x, y)` (and likewise `ψ`, `χ`). These records
therefore carry reviewed-gap evidence; the source has not been rewritten.
