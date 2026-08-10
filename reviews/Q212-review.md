# Audit Q212 — PM I, ✱2·5–✱2·521

Verdict: **A — résultat Aristotle complet audité, intégré en attente de CI**. Q205 et Q211 sont
kernel-checkés; pour Q211, le commit
`d41b8a34bdcaad43e4f753e775a7bd2c79b45add` a passé le step « Build and
kernel-check the edition » du run GitHub Actions
`https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31422968106`.
Le prompt reproduit byte-for-byte les corps certifiés de toute la fermeture de
dépendances requise, notamment ✱2·17 et ✱2·47–49, sans axiome ni hypothèse.
Le résultat terminal `757034c8-3d4e-427d-ac3f-3eff3fd0c8c0` couvre exactement
les quatre identifiants canoniques du pipeline, sans ✱2·53. Archive immuable:
`aristotle/results/Q212-final.tar.gz`; SHA-256
`3c922a2fe44109e92ed5da99806793f88cdc963258b2b7f0be3520f7c4f6540c`.
Source: première édition, vol. I, p. 112, feuille 134.

Les portées exactes sont `¬(p→q)→(¬p→q)`, `¬(p→q)→(p→¬q)`,
`¬(p→q)→(¬p→¬q)` et `¬(p→q)→(q→p)`. Les trois premières sont les instances
imprimées de ✱2·47–49; ✱2·521 compose ✱2·52 et ✱2·17.

Wikisource commet une erreur numérique certaine en ✱2·52: `p⊃¬q` au lieu de
`¬p⊃¬q`, lecture nette du scan et de Gutenberg. Classification
`digital-witness-error`, jamais `sic`. Aucun défaut de l'imprimé. Confiance haute.
Le résultat ne contient ni `sorry`, ni `admit`, ni axiome ajouté, ni `unsafe`,
ni `Classical`. La composition imprimée ✱2·52·17 est développée via ✱2·05 et
le détachement, sans élargissement sémantique.
