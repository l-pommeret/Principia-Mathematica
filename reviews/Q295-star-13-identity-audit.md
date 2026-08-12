# Q295 — ✱13·21 and ✱13·22 exact integration audit

The canonical witnesses are first-edition volume I scan leaves 201–202,
printed pages 179–180.  The Lean declarations retain both variable sorts, the
two displayed identities, the binary propositional function, and respectively
the formal universal implication and existential conjunction.

Lean equality supplies precisely the substitution and reflexivity used by the
printed identity-elimination results.  ✱13·21 is proved by specializing at
`z = x`, `w = y` and by equality elimination in the reverse direction.
✱13·22 is proved by eliminating, or constructing, the witnesses `x` and `y`.
No inhabitance, decidable equality, classical logic, axiom, placeholder, or
unsafe declaration is introduced.

The printed dependency chains through ✱11·62/✱13·191 and
✱11·55/✱13·195 are retained as source history.  The exact endpoints close
directly from Lean equality, so the metadata records them as audited relaxed
closures with no added dependency.
