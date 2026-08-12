# Q265 canonical target gate

The five exact statements are now represented in the separate canonical
module `Star10Q265Targets.lean`. It embeds the existing apparent-variable
matrices and primitive binders into `CanonicalOrderedFormula.Raw`; implication,
product, and equivalence are only their PM definitions.

`Star10Q265Kernel.lean` now closes two exact proof chains. ✱10·27 reuses the
complete closed ✱9·21 normalization and records only the fixed ✱10·02 target;
✱10·28 analogously reuses the closed ✱9·22 existential monotonicity proof.
Neither wrapper exports detachment or Raw reification.

`Star10Q265Prerequisites.lean` now closes the exact ✱10·22 contract over its
printed ingredients ✱10·1, ✱3·26, ✱10·11, ✱10·21, and ✱3·27.  On that fixed
bridge, ✱10·271 uses the two orientations of ✱10·27 and ✱10·281 the two
orientations of ✱10·28.  The wrappers export neither generic Raw detachment
nor conversion.

✱10·35 still requires closed ✱10·23 and ✱10·11·21 and therefore remains an
exact target only. The homogeneous batch remains `prepared` pending that last
item; no duplicate metadata item for ✱10·22 was introduced.
