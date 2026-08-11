# Audit Q221 — PM I, ✱3·1–✱3·14

Verdict: **A — contexte exact kernel-checké, éligible à une tâche Aristotle**.
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
