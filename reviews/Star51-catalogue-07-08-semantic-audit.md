# ✱51 catalogues 07–08 — strict source/Lean semantic audit

The ten literal statements PM1:✱51·3 through ·42 on first-edition printed
pages 360–361 (scan leaves 382–383) were checked against Project Gutenberg
78050 and the complete declaration types and proof bodies in
`Star51RemainingKernel.lean`.

All five items in catalogue 07 are exact. The local interpretations of class
difference, intersection, inclusion, complement, the null class, and a unit
class are pointwise definitions. Declaration ·3 is the printed membership
equivalence by reduction. Declaration ·31 preserves the entire four-term chain
as three adjacent equivalences and reads `∃!α∩ιʻx` as nonemptiness of that
class, consistently with PM's existence notation. Declarations ·34–·36 preserve
the orientation and both sides of their membership/complement inclusions.

All five items in catalogue 08 are exact as well. Declaration ·37 is the
pointwise class abstraction of unit-class inclusion. Declaration ·4 correctly
requires both existence of `A` and inclusion in the singleton; ·401 includes
the null alternative and the singleton alternative. Finally ·41 is exactly the
fixed-first-member union equivalence, while ·42 retains the direction and both
pairing alternatives of the printed implication.

The promoted set is exactly 10/10, in place, with no refused sidecar and no
duplicate proposition ID. Printed dependency graphs record every numbered
citation in the Gutenberg display and demonstrations. Direct Lean proposition
dependencies are ✱51·37 → ✱51·2 and ✱51·401 → ✱51·4; the other
proof bodies have no direct numbered theorem reference (the local private pair
helper used by ·41/·42 is not itself a numbered proposition).
