# Audit Q246 — PM I, ✱5·23–✱5·25 and ✱5·3

Verdict: **PARTIEL — ✱5·25 et ✱5·3 canoniques; ✱5·23–24 bloqués par Q245**. Source: first edition, vol. I,
p. 130, leaf 152; SHA-256
`c91b873037f45daeac9ca2a94f88cbb60dbe0134338c53292f859712a17fb497`.

The terminal archive `Q246-task-1cbc700b-final.tar.gz` (SHA-256
`ca7a0062158dd442b909500ba00c59b36e45120eac3987b0747a315889482a2d`)
builds only in its archive-local `Deriv` architecture and is therefore not
promotable byte-for-byte. Its dependency audit confirms that ✱5·23 requires
✱5·18 and ✱5·22, and ✱5·24 then requires ✱5·22 and ✱5·23. Those Q245
declarations are not yet present in the canonical module. By contrast,
the exact unconditional ✱5·25 and ✱5·3 targets are already kernel-checked in
`Star5Kernel.lean`; no duplicate declaration is introduced here.

The exact scopes are `(p≡q)≡(p.q∨∼p.∼q)`,
`∼(p.q∨∼p.∼q)≡(p.∼q∨q.∼p)`, `(p∨q)≡((p→q)→q)`, and
`(p.q→r)≡(p.q→p.r)`. The prose after ✱5·25 is canonical. `Simp`, `Comp`,
and `Syll` mean ✱3·26/·27, ✱3·43, and ✱3·33/·34. Wikisource alone omits
the star before `4·13·36` in ✱5·23: record a digital-witness variant, not
`[sic]`. No print defect is established. Confidence high.
