# Audit Q246 — PM I, ✱5·23–✱5·25 and ✱5·3

Verdict: **COMPLET — quatre cibles canoniques, en attente de CI**. Source: first edition, vol. I,
p. 130, leaf 152; SHA-256
`c91b873037f45daeac9ca2a94f88cbb60dbe0134338c53292f859712a17fb497`.

The terminal archive `Q246-task-1cbc700b-final.tar.gz` (SHA-256
`ca7a0062158dd442b909500ba00c59b36e45120eac3987b0747a315889482a2d`)
builds only in its archive-local `Deriv` architecture and was not promoted
byte-for-byte. Its four constructions were remapped to the canonical PM
calculus. `Star5Q246.lean` now supplies ✱5·18 as the exact printed prerequisite,
then ✱5·23 and ✱5·24; the already canonical ✱5·25 and ✱5·3 remain in
`Star5Kernel.lean`. No duplicate target, parallel deduction system, or
placeholder is introduced.

The exact scopes are `(p≡q)≡(p.q∨∼p.∼q)`,
`∼(p.q∨∼p.∼q)≡(p.∼q∨q.∼p)`, `(p∨q)≡((p→q)→q)`, and
`(p.q→r)≡(p.q→p.r)`. The prose after ✱5·25 is canonical. `Simp`, `Comp`,
and `Syll` mean ✱3·26/·27, ✱3·43, and ✱3·33/·34. Wikisource alone omits
the star before `4·13·36` in ✱5·23: record a digital-witness variant, not
`[sic]`. No print defect is established. Confidence high.
