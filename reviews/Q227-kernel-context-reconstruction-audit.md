# Q227 reconstruction audit — kernel-constant transplant

The terminal Aristotle archive
`aristotle/results/Q227-kernel-context-retry-01-final.tar.gz` has immutable
SHA-256
`af82d92138a35907c26544ed284a35ad945c9710f0849f4dd40cdebba0ae63b9`.
It is rejected as an integration artifact: although its three Star4 target
proof terms have the authorized direct citations, it reconstructs local
versions of `PM.FirstEdition.Volume1.Star3.star_3_2` and `star_3_47`; that
reconstruction invokes the forbidden primitive propositions ✱1·2–✱1·6.

Only the three target bodies were transplanted into
`Principia/FirstEdition/Volume1/Part1/SectionA/Star4.lean`.  Their references
are fully qualified to the existing kernel declarations in `Star3.lean`; no
archive context, packaging namespace, helper, or local Star3 declaration was
integrated.  A literal source audit finds zero occurrences of
`star_1_2`–`star_1_6`, `PM.Q227Packaging`, `Classical`, `axiom`, `sorry`,
`admit`, or `unsafe` in the transplanted Star4 source.  The remaining direct
proof citations are exactly:

- ✱4·1: ✱2·16, ✱2·17, ✱3·2, and ✱1·1/✱1·11 branches.
- ✱4·12: ✱2·03, ✱2·15, ✱3·2, ✱3·47, and ✱1·1/✱1·11 branches.
- ✱4·13: ✱2·12, ✱2·14, ✱3·2, and ✱1·1/✱1·11 branches.

The transplant awaits remote Lean CI; it is not yet a kernel-checked
promotion.
