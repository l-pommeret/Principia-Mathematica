# Audit Q209 — PM I, ✱2·36–✱2·38 et ✱2·41

Verdict: **A (réponse Aristotle acceptée, en attente de CI)**. L'archive
immuable `aristotle/results/Q209-final.tar.gz` a l'empreinte SHA-256
`927145575d1980e56313b741c8e37eef0f114d5e94fb7729684e0f9b579d5ad7`.
Les quatre cibles ✱2·36, ✱2·37, ✱2·38 et ✱2·41 sont présentes sans
modification de leur énoncé.

Sources: première édition, vol. I (1910), pp. 110–111, feuilles 132–133.
Les trois premières propositions conservent expressément les ingrédients
imprimés `Syll.Perm.Sum`; ✱2·41 conserve `Assoc`, puis `Taut.Sum`.

Q209 n'utilise ni ✱2·31, ni ✱2·32, ni ✱2·4 et demeure donc réellement
parallèle à Q208. Son résultat ✱2·38 est une dépendance obligatoire de Q210.
Le `data-tex` PG présente dans la démonstration de ✱2·36 des corruptions
évidentes (`\lor` et `p∨q` mal rendus); elles appartiennent au témoin
numérique et ne justifient aucun `[sic]` de l'imprimé. Confiance élevée.

Audit formel: aucun `sorry`, `admit`, `unsafe`, axiome auxiliaire, raisonnement
sémantique ou appel à `Classical`. Les preuves exposent les instances de
`Perm`, `Sum`, `Assoc` et `Taut` imprimées; `Syll.` est développé uniquement
par ✱2·05/✱2·06 et `PM.Derivation.detach`. Elles n'utilisent ni ✱2·31,
ni ✱2·32, ni ✱2·4. Les dépendances PM, Lean et normalisées sont consignées
dans `metadata/items/PM1-star-2-Q209.json`. La version autonome d'Aristotle
était étiquetée Lean 4.28.0 bien que le prompt demandât 4.30.0; seule la CI
GitHub du dépôt, épinglée à Lean 4.30.0, vaut certification finale.
