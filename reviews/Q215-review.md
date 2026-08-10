# Audit Q215 — PM I, ✱2·63–✱2·65

Verdict: **A — prêt pour soumission, non soumis**. Q214 et sa fermeture
transitive sont kernel-checkés au commit
`b9eb7851d644043582bdc07b67e5ad05c5af40d3` par le workflow GitHub Actions
[`31424832320`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31424832320),
terminé avec conclusion `success`, y compris le build noyau et le rejet des
placeholders et déclarations non sûres.
Source: première édition, vol. I, p. 112, feuille 134; SHA-256
`3818c499d4043461da32394ef639aae79871df6caf7fffc61d54f7bbcacbb153`.

Portées: `(p∨q)→((¬p∨q)→q)`, `(p∨q)→((p∨¬q)→p)`,
`(p→q)→((p→¬q)→¬p)`. ✱2·63 et ✱2·65 sont des instances définitionnelles;
✱2·64 conserve l'instance simultanée et Perm. Aucun `sic` ou écart de témoin.
Confiance haute.

La dépendance directe unique est ✱2·62. Sa fermeture transitive est
✱2·6, ✱2·53, ✱2·38, ✱2·12, ✱2·06, ✱2·05, ✱2·04, ✱2·03,
✱2·07, ✱2·08, ✱2·1, ✱2·11, ✱2·13, ✱2·14, les primitives ✱1·2–✱1·6
et le détachement prouvé. Le prompt contient désormais le corps accepté de
`star_2_62` byte for byte et exige les vrais corps de toute cette fermeture;
aucun axiome, hypothèse, placeholder ou principe sémantique n'est admis.
Q212 est également promu par la même CI, mais n'est pas une dépendance de
Q215 et n'est donc pas ajouté artificiellement à sa fermeture.
