# Q307 review

Leaves 212–213 (pp. 190–192), SHA-256 `fd6e3e463dd9d347c1ebad1d5ddc3bf54298377f6fa94120a3d584cf23cc63c6` and `23fcfd8a9484e82eb140b74e2b9a1f3d93d87ee89d7958c9c6cc37f35eeb9b21`, plus PG 78050, collate the four scope-sensitive loci.

`Star14Q307Kernel.lean` now represents all four loci on the contextual
description layer established at Q297. ✱14·22 evaluates `φ` at the unique
witness; ✱14·23 keeps the complete describing matrix `φ ∧ ψ` distinct from
the evaluated predicate `φ`; ✱14·24 and ✱14·241 retain the description scope
around `∀ y, φ y ↔ y = b`. In particular, no witness escapes as a globally
defined description term. The proofs require neither choice nor inhabited
types and contain no placeholder or new axiom.

Targeted Lean 4.30.0 check:

```text
lake env lean Principia/Architecture/Star14Q307Kernel.lean
```
