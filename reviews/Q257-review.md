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
new Pp.  The split Q257-24 metadata is awaiting CI.  ✱9·23 and ✱9·25 retain
their independent statuses.
