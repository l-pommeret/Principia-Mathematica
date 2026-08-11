# Q233 continuation — remove copied interface and prove the exact targets

The immediately preceding terminal archive (task
`3bfbf6c1-2bc6-4dd4-b498-6be588cf45a4`, immutable SHA-256
`d1e2a48205e5db12c4e6fe987648692cb813e1de278256a1e9e47e38ef58e5e5`)
is rejected.  It includes local copies of PM syntax/Star2/Star3/Star4 and a
`KernelLink.lean` layer, uses forbidden `Classical` in that layer, and its
fallback theorems add missing-rule hypotheses.  None of that is a proof of the
submitted unconditional targets and none may be reused as a copied or remapped
dependency.

Continue this same project.  Deliver exactly, in order, the three submitted
unconditional declarations from `Q233.md`:
`PM.FirstEdition.Volume1.Star4.star_4_43`, `star_4_44`, `star_4_45`, with
their exact signatures, the cited printed demonstrations, ✱4·43's (1), (2)
and `∼p/p` substitution, and ✱4·44's (1), (2).  No conditional target,
assumption parameter, alternate namespace, companion theorem, or selected
example is a completion.

Use only already accepted project-visible kernel bodies corresponding to the
submitted dependencies; the required ✱4·01 definition must be an accepted
body, not a declaration-only interface.  Delete/avoid every local PM copy,
local module/import, archive transplant, interface remap, `Proof.mp`, `adj`,
`syll`, generic replacement rule, semantic/equality/And/Iff proof, `Classical`,
`axiom`, `sorry`, `admit`, `unsafe`, or target change.

First inspect the existing project state.  If every dependency is already an
accepted kernel body, build direct exact proofs only.  Otherwise introduce no
surrogate code or hypotheses and return a compact per-target list of the exact
missing accepted-kernel declaration(s), including the missing rule needed for
each printed step.  Such a report is incomplete, never a successful result.
