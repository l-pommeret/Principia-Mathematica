# Q268 ✱10·23 audit

The exact left member is `∀x (¬φx ∨ p)` with `p` explicitly weakened below
the binder. Binder extraction closes it to `∀x ¬φx ∨ p`. The exact right
member is `¬∃x φx ∨ p`; the audited ✱10·01/negated-existential normalization
closes it to the same Raw formula. The Q268 certificate additionally retains
the alternative printed route through the closed ✱10·21 instance and ✱10·1
witness. No generic equivalence assertion, detachment rule, axiom, semantic
quantifier, or scope weakening is introduced. Dependency metadata is marked
relaxed because the public wrapper packages some citations behind a
theorem-specific structure.

Promotion simulation passes. Direct extraction finds ✱10·1, ✱10·21, and the
same-item prerequisite helper; normalization retains the first two and
correctly suppresses the historical self-edge. The remaining printed steps
are exactly listed as unused. Disjunction reversal and negated-existential
normalization are canonical syntax-normalization evidence, not PM theorem
edges. No status is promoted here.
