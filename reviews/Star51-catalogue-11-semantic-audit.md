# ✱51 catalogue 11 — strict source/Lean semantic audit

The two final literal statements of ✱51 on printed page 362 were compared with
the complete types and bodies of `star_51_58` and `star_51_59` in
`Star51RemainingKernel.lean`. Incomplete descriptions are interpreted
contextually: `OnlyExists A` records that a class is a singleton,
`DescriptionExists A` records its unique member, and `DescriptionApplies φ ψ`
records the unique `φ`-witness together with application of `ψ` to it.

Both items are exact. At ·58 the two printed descriptions exist and are equal
under exactly the same unique-member condition; Lean reuses the already exact
equivalence ·55. At ·59 the two printed contextual applications normalize to
the same `DescriptionApplies φ ψ` condition. Its reflexive Lean proof is not a
placeholder: the two syntactically different incomplete descriptions have the
same explicitly defined contextual semantics.

The promoted set is 2/2, in place, and no refused sidecar is created. The
literal source blocks contain no bracketed citations. The only numbered Lean
edge is ·58 → ·55; it is normalized and documented as a narrow relaxed-closure
edge. Declaration ·59 is definitional and has no numbered dependency.
