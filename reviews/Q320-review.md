# Q320 review — ✱20·23–31

Leaf 225 (p. 203), SHA-256
`ea1ff710c6994818914e034cc0d164970475dfc015e69538b9bb827b56253ac8`,
and PG78050 agree on all five statements. ✱20·3 and ✱20·31 are canonical
here; their p. 199 occurrences are summaries only.

The formalization extends the eliminative architecture of ✱20·01–02.
`ClassEquivalent` is pointwise formal equivalence of two defining matrices,
and `Member x ψ` reduces to the matrix value `ψ x`. Thus no class-valued term,
untyped universal class, `Set`, choice principle, or function extensionality is
introduced. ✱20·23–24 are the two printed transitivity arrangements; ✱20·25
uses the universally quantified comparison exactly; ✱20·3 and ✱20·31 are the
membership and extensionality reductions.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star20Q320Kernel.lean`
