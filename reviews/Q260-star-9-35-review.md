# Q260 ✱9·35 kernel review

The source says “Proof as above,” referring to ✱9·34. The existential copy
uses ✱1·3 and ✱9·13 for the pointwise injection, ✱9·22 for existential
monotonicity, and ✱9·05 to rewrite `∃x (p ∨ φx)` as `p ∨ ∃x φx`.

The public result is the exact narrow `Star935KernelAssertion`, not an
`OrderedAssertion`. It contains the closed ✱9·22 witness and an explicit
scope-normalization certificate for the final ✱9·05 step. No oracle,
classical reasoning, generic detachment, or target constructor was added.

Status: awaiting CI.
