# Audit Q218 — PM I, ✱2·73–✱2·76

Verdict: **A FOR TARGET AND ORDERED CONTEXT — pending remote kernel CI**.
Canonical source: first
edition, vol. I, p. 113, leaf 135; SHA-256
`0015ae56c8a9c1eedab541d07e06d683c499319b60fa021d088077535f93f2f0`.

Scopes: `(p→q)→(((p∨q)∨r)→(q∨r))`,
`(q→p)→(((p∨q)∨r)→(p∨r))`,
`(p∨q)→((p∨(q→r))→(p∨r))`, and
`(p∨(q→r))→((p∨q)→(p∨r))`. The `∨` chains are left-associated. The
reference `✱2·621·38` names ✱2·621 and ✱2·38; it is not a malformed number.
No print defect is established in these four items. Confidence high.

The parser-generated batch manifest gives every target an independent exact
whitelist. ✱2·73 uses only ✱2·621, ✱2·38 and the reviewed ✱1·11 global
convention. Each later target may use only its immediately preceding local
target plus its own printed aliases/references. Local targets are absent from
the external context closure. The 10.9 kB isolated context and the full
Aristotle prompt are reproducible from `metadata/constrained_batches/Q218.json`.
Submission remains forbidden until GitHub CI kernel-checks that context.
