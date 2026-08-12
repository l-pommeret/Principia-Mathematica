# Audit Q244 — PM I, ✱5·15–✱5·17

Verdict: **BLOCKED — seven cited canonical declarations still absent**. Source: first edition, vol. I,
p. 129, leaf 151; SHA-256
`8ad683eab8e99f0aab97f8a6b1e0179c28e354a9f678c4df2cd1e2fb2d510f4a`.

Scopes are `(p≡q)∨(p≡∼q)`, `∼((p≡q).(p≡∼q))`, and
`((p∨q).∼(p.q))≡(p≡∼q)`. The long ✱5·16 proof retains its simultaneous
substitution and all three intermediates. No print defect or material digital
error is established. Confidence high.

The terminal kernel-link archive
`aristotle/results/Q244-kernel-link-retry-01-final.tar.gz` (SHA-256
`a538b87549461291192f29231c6b16ceaebfa2296beb641e23a9dba5c4965c44`)
contains exact proof bodies, but its apparent theorems are conditional on
link-point parameters.  They therefore do not prove the unconditional
canonical targets and cannot be promoted.

Local reconciliation against the current canonical tree reduces the archive's
original sixteen missing link points to seven declarations:

- ✱3·43: `PM.FirstEdition.Volume1.Star3.star_3_43`;
- ✱4·21, ✱4·41, ✱4·51, ✱4·61, ✱4·63, ✱4·65 in
  `PM.FirstEdition.Volume1.Star4`.

The theorem-level obstruction is exact: ✱5·15 still needs ✱4·41 and ✱4·61;
✱5·16 still needs ✱3·43, ✱4·51, and ✱4·65; ✱5·17 still needs ✱4·21 and
✱4·63.  Every other link point now has a canonical theorem with the required
statement.  Importing the archive's parked local Star3/Star4 modules would
duplicate canonical material and violate the requested canonical-only gate.

Verification on 2026-08-12: the Q244 interface elaborates and
`lake build Principia.FirstEdition.Volume1.Part1.SectionA.Star5Kernel` succeeds
with Lean 4.30.0.  No unconditional Q244 declaration was added.
