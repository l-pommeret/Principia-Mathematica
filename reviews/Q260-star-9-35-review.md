# Q260 ✱9·35 kernel review

The source says “Proof as above,” referring to ✱9·34. The existential copy
uses ✱1·3 and ✱9·13 for the pointwise injection, ✱9·22 for existential
monotonicity, and ✱9·05 to rewrite `∃x (p ∨ φx)` as `p ∨ ∃x φx`.

The public result is the exact narrow `Star935KernelAssertion`, not an
`OrderedAssertion`. It contains the closed ✱9·22 witness and an explicit
scope-normalization certificate for the final ✱9·05 step. No oracle,
classical reasoning, generic detachment, or target constructor was added.

GitHub Actions run `31578445311` succeeded at immutable commit
`d9fe80c3d20bd5aef361b729f9f422ba17591da5`. This certifies only the narrow
`Star935KernelAssertion`, including its explicit ✱9·22 and ✱9·05 inputs.
