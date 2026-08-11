# Audit Q221 — PM I, ✱3·1–✱3·14

Verdict: **ARCHIVE DE CONTINUATION ACCEPTÉE — intégration en attente de CI Lean distante**.
La CI Lean
[`31452200404`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31452200404)
a réussi sur le commit `85865c7a46df398f2f44ebc6a8c867f756dc7ad9`, y compris
le contexte isolé Q221. L'audit Terra a restauré le premier point de portée
imprimé de ✱3·12 et
montré que le nom historique `Transp` couvre ✱2·15, ·16 et ·17. La whitelist
de ✱3·13 autorise donc ✱2·15 avec le détachement ✱1·11; celle de ✱3·14 rend
explicites la double négation ✱2·12, la composition ✱2·06 et le détachement
que la macro imprimée masque. Sources: first edition, vol. I,
pp. 116–117, leaves 138–139. SHA-256: leaf 138
`c18eb6890dc92335e8df8773cbd46b8e98c2e550cdcb01f91a397bed27e9958b`;
leaf 139 `1b819017782765dda67ae70a26b49055f1a636edbc04ed5aa52985fd018f047c`.

Scopes: `p·q→¬(¬p∨¬q)`, its converse,
`(¬p∨¬q)∨(p·q)`, `¬(p·q)→(¬p∨¬q)`, and its converse. The first
three-place disjunction is left-associated under ✱2·33. No print defect is
established in these five items. Confidence high.

The first immutable archive, task `10f781a5-9c34-4aa4-9608-f0934778ac3f`, is
`aristotle/results/Q221-final.tar.gz`, SHA-256
`db4dfb80d6c00c81d5f22e5075705002c0b1c91868b22f5e8ceebd08d373c339`.
Its safety audit found no placeholder, axiom or unsafe escape hatch (only the
reported `Classical` harness exception), but its reconstruction audit rejected
✱3·1, ✱3·11 and ✱3·14: the former two leave printed ✱3·01 uncovered and the
last bypasses both printed citations ✱3·1 and `Transp` through direct ✱2·12.

The same project’s fidelity-only continuation, task
`80b9650e-4ee8-4b4a-8523-c75a04a2a58a`, returned the immutable archive
`aristotle/results/Q221-retry-01-final.tar.gz`, SHA-256
`aa7a9bca9bceadd9b58fda40b04207a19dff54b25c5a674c055c4de5afb0c8b8`.
It contains neither `sorry`, `admit`, axioms nor unsafe escape hatches; the
sole `Classical` occurrence is in Aristotle’s generated harness, outside the
five returned declarations. The constrained reconstruction audit
[`Q221-reconstruction-audit.json`](Q221-reconstruction-audit.json) is strict
for all five targets. In particular, ✱3·1 and ✱3·11 unfold ✱3·01 explicitly;
✱3·13 uses ✱3·11 then the ✱2·15 `Transp` form; and ✱3·14 follows ✱3·1,
✱2·16, ✱2·12, ✱2·06 and detach/✱1·11 in that order. No excess permission or
uncovered printed citation remains. The imported source remains **awaiting
remote kernel CI**; no Q221 theorem is promoted until that CI succeeds.
