# Q411 strict semantic review — PM II ✱102·01, p. 26

**Verdict: strict equivalence passed; awaiting CI.** First-edition p. 26,
Commons leaf 66, is canonical; its derivative SHA-256 is
`f55cda3ec4d521d941e7c6ace4c94adb89ba4be3459f06e329ab49af36cbce44`.
PG78255 independently witnesses the definition
`NCᵝ(α) = DʻNc(αᵦ)`.

The typed reconstruction interprets `Nc(αᵦ)` as the relation taking a class
`b : Class B` to its cardinal fibre `Nc b : Class (Class A)`. Its domain is
therefore, extensionally, the class of `μ` for which some `b` satisfies
`μ = Nc b`. This is exactly the definition of `NC` in
`Star102OpeningKernel.lean`, and `star_102_01` exposes the corresponding
membership biconditional. The move from PM's class equality to pointwise
membership equivalence is extensional only: it adds no hypothesis, drops no
case, and does not strengthen or weaken the definition.

As a definition, ✱102·01 has no printed proposition citation. The Lean theorem
closes by definitional equality (`Iff.rfl`) and likewise has no numbered Lean
dependency. Both direct dependency graphs are empty. The item is promoted to
`awaiting-ci`; its commit and CI run remain pending.
