# Q265 canonical target gate

The five exact statements are now represented in the separate canonical
module `Star10Q265Targets.lean`. It embeds the existing apparent-variable
matrices and primitive binders into `CanonicalOrderedFormula.Raw`; implication,
product, and equivalence are only their PM definitions.

`Star10Q265Kernel.lean` now closes two exact proof chains. ✱10·27 reuses the
complete closed ✱9·21 normalization and records only the fixed ✱10·02 target;
✱10·28 analogously reuses the closed ✱9·22 existential monotonicity proof.
Neither wrapper exports detachment or Raw reification.

✱10·271 and ✱10·281 still require the printed ✱10·22 equivalence-product
bridge, and ✱10·35 additionally requires closed ✱10·23 and ✱10·11·21.
Those prerequisites do not yet exist canonically, so these three remain
targets only. The homogeneous batch remains `prepared` until it can be split
without duplicating IDs or completed as a whole.
