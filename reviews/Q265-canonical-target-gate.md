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

`Star10Q265FinalPrerequisites.lean` reuses the independently closed canonical
✱10·23 normalization and represents `✱10·11·21` correctly as a composed rule use rather than
inventing a separately numbered proposition.  With these, ✱10·35 is closed
over the exact printed ✱3·26/✱10·11/✱10·23/✱3·27/✱10·28/✱3·2/✱10·11·21
chain.  The homogeneous batch is now `awaiting-ci`; no
duplicate prerequisite metadata IDs were introduced.
