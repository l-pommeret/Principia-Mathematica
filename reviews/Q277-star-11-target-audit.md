# Q277 — ✱11·07, ✱11·1, ✱11·11–14

The diplomatic source and both witnesses agree on the six p. 159 items. The
Lean module gives their exact binary-variable endpoints: two explicit
quantifiers, a capture-safe transposition, two successive instantiations, and
the literal premise/conclusion contracts of the metalinguistic rules.

All six items remain `prepared`. The current kernel exposes ✱10·1 and ✱10·11
only for one-place `Apparent` assertions. It has no constructor that lifts
those primitive judgements through a second assigned quantifier, and ✱11·07
is itself the new binary-permutation Pp. Treating target reflexivity or a
Lean-level function as their proof would silently add precisely the higher
assertion rule that PM introduces here. Consequently this batch is exactly
target-complete but not kernel-checked.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star11Q277Targets.lean`
