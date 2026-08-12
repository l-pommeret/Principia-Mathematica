# Q262/Q262a canonical target adapter

The six printed formulae now have exact closed targets in
`Q262CanonicalTargets.lean`. The adapter reuses the canonical `Raw` carrier,
the existing embeddings of elementary/apparent/first-order syntax, and PM's
defined implication. It adds no assertion constructor or inference rule.

No theorem is promoted yet: proving these targets requires source-scoped
bridges from the already closed ✱9·21/22 witnesses through the mixed-order
outer implications. Adding a generic Raw detachment rule would exceed the
printed demonstrations, so the metadata remains honestly `prepared`.
