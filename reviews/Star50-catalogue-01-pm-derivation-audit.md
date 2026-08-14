# ✱50 catalogue-01 PM-derivation audit

This five-item audit applies the ✱1–✱5 and T1–T9 standard after reading the
append-only coordination record in `dialogue.md`. The existing typed relation
model is useful secondary semantics, but it is not itself the primary PM
formalization.

## Verdict

No item reaches `pm-derivation-v1`. ✱50·01 and ·02 are printed definitions
(`Df`). Following the accepted rule for ✱23, they must remain eliminable
definitions and must not be turned into constructors of a derivation relation.
Their Lean definitions are exact and axiom-free, but they are not theorem
judgements and therefore cannot satisfy T2–T4 as v1 propositions.

Theorems ✱50·1, ·11, and ·12 are exact at the secondary typed-`Prop` level, but
their declarations close by `Iff.rfl`, `Iff.rfl`, and `rfl`. The repository has
no accepted relational formula AST, concrete reading type, or inductive PM
derivation relation covering ✱50 and its printed predecessors ✱21/✱23. Hence
these declarations contain no object-language judgement and no chain of PM
rule constructors. Promoting them would reproduce the semantic-wrapper failure
documented in `dialogue.md`. All five items are honestly returned to
`prepared`, with definitions blocked as non-judgements and propositions blocked
for absence of a PM derivation.

## Dependency graphs rebuilt from zero

The printed graph is preserved verbatim:

- ·01 and ·02 have no bracketed proposition citation;
- ·1 cites ✱21·3 and ✱50·01;
- ·11 cites ✱23·35, ✱50·1, and ✱50·02;
- ·12 cites ✱50·11 and ✱21·33.

The actual Lean-source graph contains only definitional constants: `J` calls
`I`; ·1 calls `I`; ·11 calls `J`; and ·12 calls `J`. There are no calls to PM
judgement theorems or derivation constructors. Normalization therefore remains
·02→·01, ·1→·01, ·11→·02, and ·12→·02. Existing explicit relaxation records
correctly distinguish those real definitional edges from PM's printed proof
routes. No new edge is inferred from prose or from the semantic truth of a
formula.

Targeted kernel queries confirm that all five current declarations are free of
global axioms. That fact makes them suitable secondary lemmas, but it does not
repair T3/T4 or elevate them to v1.
