# Q260b ✱9·37 kernel review

The “Similar Proof” instantiates ✱1·4 pointwise, closes it using ✱9·13 and
existential monotonicity ✱9·22, then applies the two directions of ✱9·05.
`Star937KernelAssertion` retains the actual elementary derivation, the exact
✱9·22 witness, and separate scope certificates. It is not reified as an
`OrderedAssertion`; no oracle or generic detachment was introduced.

GitHub Actions run `31581077931` succeeded at immutable commit
`e322d45b5fadd0091b652d0a751a10b737abdbae`, certifying this exact narrow
judgement only.
