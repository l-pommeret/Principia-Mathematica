# Audit Q243 — PM I, ✱5·11–✱5·14

Verdict: **✱5·11–✱5·14 intégrés dans le module noyau canonique**. Source: first edition, vol. I,
p. 129, leaf 151; SHA-256
`8ad683eab8e99f0aab97f8a6b1e0179c28e354a9f678c4df2cd1e2fb2d510f4a`.

All four disjunctions have the printed scopes. ✱5·11–✱5·13 were already
kernel-checked in `Star5Kernel.lean`. The terminal Q243 archive
`Q243-task-d115456b-final.tar.gz` (SHA-256
`be844c680502264617f4f6ba8a38d71e1f832ccb1412fed27a0ac96d98adf7e9`)
supplies the missing ✱5·14 construction, but only conditionally on explicit
kernel-link hypotheses. Its proof body has therefore been promoted against
the actual canonical dependencies: primitive Add (the printed `Simp`
instance), ✱2·16 (`Transp`), ✱2·21, primitive Sum for composition, and ✱2·54
for disjunctive packaging. The resulting theorem is unconditional in the
canonical module. No print defect or material digital corruption is
established. Confidence high.
