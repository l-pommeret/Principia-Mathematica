# Audit Q216 — PM I, ✱2·67–✱2·69

Verdict: **A — complet et apparemment correct; éligible Aristotle**. Le
contexte complet de Q206, Q212, Q213 et Q214 est intégré au commit
`b9eb7851d644043582bdc07b67e5ad05c5af40d3` et vérifié par le noyau dans la
run GitHub Actions `31424832320` (conclusion `success`). Le prompt autonome
reproduit les vrais corps certifiés, notamment ✱2·05/✱2·06 depuis Q212 et
✱2·62 depuis Q214, ainsi que leur clôture de dépendances. Sources: première
édition, vol. I, pp. 112–113, feuilles 134–135.
SHA-256: feuille 134
`3818c499d4043461da32394ef639aae79871df6caf7fffc61d54f7bbcacbb153`;
feuille 135
`0015ae56c8a9c1eedab541d07e06d683c499319b60fa021d088077535f93f2f0`.

Portées: `((p∨q)→q)→(p→q)`, `((p→q)→q)→(p∨q)`,
`((p→q)→q)→((q→p)→p)`. ✱2·67 doit conserver les lignes (1), (2) et le
Syll final; ✱2·68 conserve l'instance `¬p/p` et ✱2·54; ✱2·69 conserve Perm
et l'instance de ✱2·62. Aucun défaut imprimé ni divergence substantielle.
Confiance haute. Cible Lean sûre: les trois énoncés canoniques exacts dans le
système syntaxique PM, sans axiome auxiliaire ni affaiblissement de portée.
