# Audit Q216 — PM I, ✱2·67–✱2·69

Verdict: **A — accepté et kernel-checké**. Le
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

## Audit du résultat Aristotle

Verdict: **A — accepté et kernel-checké**. Projet
`5bbfa176-bd5a-4f14-9c7d-dafd0d9f035d`, tâche
`dfa4cf2e-4dbc-4cfc-9241-eb769b65672f`, statut terminal `COMPLETE`.
L’archive immuable `aristotle/results/Q216-final.tar.gz` a pour SHA-256
`552480353fdd94dce2c73a20ca73938cb7c8c060b600e58bf21eed8015952e30`.

Les trois déclarations correspondent exactement aux portées canoniques.
✱2·67 conserve `line1`, `line2`, puis leur Syll final; ✱2·68 conserve
l’instance `∼p/p` de ✱2·67 puis ✱2·54; ✱2·69 conserve Perm et l’instance
exacte `star_2_62 q p`. La clôture n’emploie que les dépendances déclarées,
les corps certifiés de ✱2·05/✱2·06 et `PM.Derivation.detach`. Recherche
négative confirmée pour `sorry`, `admit`, nouvel `axiom`, `unsafe`,
`Classical`, hypothèse ajoutée, sémantique ou cible rétrécie. Les preuves,
lectures et transcriptions diplomatiques sont intégrées. La CI du dépôt a
vérifié l’intégration exacte au commit
`2280728f3f9cad6735b2ec7f8987db4c16277499`, dans le workflow GitHub Actions
[`31427351077`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31427351077),
conclusion `success`. Le statut final est `kernel-checked`.
