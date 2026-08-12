# Audit Q257 — PM I, ✱9·23, ✱9·24 and ✱9·25

Verdict: **PREPARED — Q256 kernel context required**. Source: first edition,
vol. I, p. 140, leaf 162. Targets and printed citations are exact: universal
identity `[Id.✱9·13·21]`, existential identity `[Id.✱9·13·22]`, and the
distribution from ✱9·23 plus definitional ✱9·04. Even if the first two
formulae normalize reflexively in Lean, their historical derivations must be
retained so the dependency graph remains PM's. No print or digital-witness
defect is established for these items. Confidence high.

## ✱9·24 closed existential self-instance

`Star924Kernel.derive` specializes the completed source-audited
`Star922KernelAssertion` only at `φ = φ`.  This is exactly the printed
`Id.✱9·13·22` route: the elementary identity and fixed ✱9·13 are retained in
the certified ✱9·22 chain, rather than reintroduced as a generic rule.  Its
result remains the narrow closed `Star922KernelAssertion φ φ`, not an
`OrderedAssertion` reification; it adds neither generic Raw detachment nor a
new Pp.  GitHub Actions run `31575922684` succeeded at immutable commit
`a773a806b9759f571ce5ddaaa781d28553fc11b5`; it certifies both narrow
judgements ✱9·23 and ✱9·24, not an `OrderedAssertion` reification.  ✱9·25
is now the exact closed `Star925Kernel.derive` judgement: it uses only the
fixed ✱9·23 self-instance at `p∨φ` and the explicit definitional ✱9·04
spelling. GitHub Actions run `31577423330` succeeded at immutable commit
`125839b146e32632b67146cbe46d71528b0798d4`; it certifies this narrow
Star925Kernel judgement only, with no generic conversion rule.
