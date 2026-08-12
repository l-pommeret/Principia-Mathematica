# Q265 canonical target gate

The five exact statements are now represented in the separate canonical
module `Star10Q265Targets.lean`. It embeds the existing apparent-variable
matrices and primitive binders into `CanonicalOrderedFormula.Raw`; implication,
product, and equivalence are only their PM definitions.

This is a syntax integration, not a proof claim. The historical dependencies
✱10·14/·1/·21/·22/·23/·28 are not yet available as closed canonical
derivations, so no assertion constructor, axiom, or semantic shortcut is
introduced and the item status remains `prepared`.
