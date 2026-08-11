# Audit Q223 — PM I, ✱3·26, ✱3·27, ✱3·3, ✱3·31

Verdict: **A — kernel-checked relaxed reconstruction with printed gaps
recorded**. Source: first edition, vol. I,
p. 117, leaf 139; SHA-256
`1b819017782765dda67ae70a26b49055f1a636edbc04ed5aa52985fd018f047c`.

Scopes: `p·q→p`, `p·q→q`, `(p·q→r)→(p→q→r)`, and
`(p→q→r)→(p·q→r)`. The names `Simp`, `Exp`, and `Imp` label these
proved propositions; none is a primitive inference rule. No print defect is
established. Confidence high.

The strict reconstruction was impossible at ✱3·27 and ✱3·31: each printed
chain ends with `Prop` after two cited implications, but `Prop` grants no
primitive proof permission. The strict archive `d1c27a…2487` was therefore
rejected. The approved continuation adds exactly one Sum/✱1·6 composition at
each of those two loci; no other source gap is licensed. The ✱1·11 detachment
convention is recorded separately for asserted-implication application.

The final four declarations were integrated and remote Lean CI kernel-checked
the isolated contexts and full edition at commit
`2af0252ddcd92a53a2493a788cb64426e262a0b2`, GitHub run
[31461909552](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31461909552),
with conclusion `success`. The generated reconstruction audit
[`Q223-reconstruction-audit.json`](Q223-reconstruction-audit.json) preserves
the strict-event failures as evidence and records the two approved ✱1·6 uses.
The central anomaly register classifies this as
`incomplete-printed-citation/implicit-composition-gap`; it is not an official
PM erratum and changes neither the diplomatic text nor its AST.
