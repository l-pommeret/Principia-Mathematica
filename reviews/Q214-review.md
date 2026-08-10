# Audit Q214 — PM I, ✱2·6–✱2·621

Verdict: **A — prêt pour soumission**. Q209, Q213 et leur clôture transitive
de dépendances sont certifiés par GitHub CI. Le prompt autonome reproduit byte
for byte les corps acceptés depuis le commit
`d41b8a34bdcaad43e4f753e775a7bd2c79b45add`; le run
[`31422968106`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31422968106)
est terminé avec conclusion `success`, y compris « Build and kernel-check the
edition » et « Reject placeholders and unsafe declarations ».
Source: première édition, vol. I, p. 112, feuille 134; SHA-256
`3818c499d4043461da32394ef639aae79871df6caf7fffc61d54f7bbcacbb153`.

Portées: `(¬p→q)→((p→q)→q)`, `(p→q)→((¬p→q)→q)`,
`(p∨q)→((p→q)→q)`, `(p→q)→((p∨q)→q)`. La démonstration de ✱2·6 doit
conserver ses deux lignes numérotées et la composition finale; ✱2·61 et
✱2·621 sont Comm, ✱2·62 est le Syll de ✱2·53 et ✱2·6. Aucun défaut imprimé
ou témoin divergent. Confiance haute.

Audit du prompt: quatre cibles et seulement quatre, ✱2·6–✱2·621. La clôture
autonome contient les définitions complètes, le corps certifié de `detach`,
les corps certifiés de ✱2·04–✱2·08, ✱2·1, ✱2·11–✱2·14, ✱2·38 et ✱2·53.
Les dépendances directes de Q214 sont donc fermées transitivement jusqu’aux
constructeurs primitifs ✱1·1–✱1·6, sans déclaration auxiliaire opaque. Le
SHA-256 du prompt final est
`e459df2cb3dc3d4561c55d46a517b13525288a1039890ac9f06151eba0210797`.
Aucun `sorry`, `admit`, nouvel axiome, `unsafe`, `Classical` ou argument
sémantique n’est fourni.

## Audit du résultat Aristotle

Verdict: **A — accepté, en attente de CI**. Projet
`ddec702d-934f-4174-8025-c1019f2c6d2f`, tâche
`b47500d3-d2f2-4e46-b47c-eb8271aac195`, statut terminal `COMPLETE`.
L’archive immuable `aristotle/results/Q214-final.tar.gz` a pour SHA-256
`ce0d2fad17bd501076cab0f88c1d03a192d2c9cca860200543b77734b7579709`.

Les quatre déclarations ont exactement les cibles demandées. ✱2·6 conserve
`line1`, `line2`, puis la composition par le corps fourni de ✱2·06; ✱2·61 et
✱2·621 détachent les instances exactes de ✱2·04; ✱2·62 compose ✱2·53 et
✱2·6 via ✱2·06. La clôture Lean ne contient que les dépendances déclarées et
`PM.Derivation.detach`. Recherche négative confirmée pour `sorry`, `admit`,
nouvel `axiom`, `unsafe`, `Classical`, hypothèse ajoutée, sémantique ou cible
rétrécie. Les preuves et lectures diplomatiques sont intégrées; le statut
reste `awaiting-ci` conformément à l’interdiction de Lean local et d’action Git.
