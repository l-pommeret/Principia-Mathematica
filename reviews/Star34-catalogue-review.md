# ✱34 v1 PM-judgment audit — first five

This audit uses the `Star2` standard: a complete proposition requires a PM
object-language formula and a kernel-checked derivation judgment. A theorem in
Lean's ambient `Prop` is useful secondary evidence but is not a PM proof.

The source graph was rebuilt from the canonical Gutenberg demonstration.
Definitions ·01–·03 have no numbered proof edges. Proposition ·1 cites
✱21·3 and definition ✱34·01. Proposition ·11 starts from ✱34·1 and
✱32·18·181, then uses ✱22·33 and ✱24·5. These are historical
edges only: neither architecture theorem calls a numbered Lean derivation.

All five items are blocked in v1. The definitions lack canonical
object-language declarations. The declarations for ·1 and ·11 are closed and
extensionally correct `Prop` equivalences, but both are proved by `rfl` over a
semantic relation model; neither has type `⊢ₚ ...` nor constructs a
`PM.Derivation`. Their former CI evidence therefore does not establish the v1
completion criterion. The five unique records remain `prepared` in one
homogeneous blocked artifact, with the `Prop` declarations retained explicitly
as secondary evidence.

No claim is made here about ✱34·12 or later loci.
