# Audit Q254a (machine ID Q254) — PM I, ✱9·07 and ✱9·08

Verdict: **A — ARISTOTLE COMPLETE; EXACT ALIASES INTEGRATED, AWAITING REPOSITORY CI**. Source: first edition, vol. I, pp. 135–136,
leaves 157–158.

The exact targets are the two direction-sensitive nested-binder definitions.
Both put universal `x` outside existential `y`; ✱9·07 has matrix `φx∨ψy`,
whereas ✱9·08 has `ψy∨φx`. The accepted generic operations take renaming and
disjunction for one fixed matrix order and therefore honor PM's explicit
extension when the two functions are not both elementary, without inventing
an all-orders universe. The two de Bruijn insertions distinguish outer and
inner variables capture-freely. Specialized reductions are `rfl`, and the
prompt requests only two editorial aliases.

No PM error is established. Wikisource's `unchaged/unchanged` is digital
only. Target/context audit A with high confidence. The former gates are
satisfied at commit `73b0a321aaaa8cd865b867572b89f3bf5eb607a3`, CI
[31439710731](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31439710731):
the higher-order operations and integrated Q253 are kernel-checked together.

Aristotle project `f34aa4c5-87af-479e-91c6-7dcc30509d26`, task
`5e0a20fa-1cd5-4345-b0e7-43bada2a5501`, completed successfully. The immutable
archive `aristotle/results/Q254-final.tar.gz` has SHA-256
`8695922974804f7b381f76db5be55cb35d3e7b490e0a53ea06b508341c9c24c5`.
The generic archive auditor found no forbidden target construct; `Classical`
occurs only in Aristotle's generated compilation harness.

As in Q253, Aristotle reconstructed an incompatible local syntax context. That
context and its checks are rejected. The two requested aliases themselves are
byte-for-byte the requested declarations and have been integrated against the
repository's already kernel-checked API. Final acceptance therefore requires a
fresh repository CI run; until then the metadata remains `awaiting-ci`.
