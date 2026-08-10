# Audit Q212 — PM I, ✱2·5–✱2·521

Verdict: **A — prompt autonome audité, prêt à soumettre**. Q205 et Q211 sont
kernel-checkés; pour Q211, le commit
`d41b8a34bdcaad43e4f753e775a7bd2c79b45add` a passé le step « Build and
kernel-check the edition » du run GitHub Actions
`https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31422968106`.
Le prompt reproduit byte-for-byte les corps certifiés de toute la fermeture de
dépendances requise, notamment ✱2·17 et ✱2·47–49, sans axiome ni hypothèse.
Aucune soumission Aristotle n'a été effectuée. Source: première édition, vol.
I, p. 112, feuille 134; SHA-256
`3818c499d4043461da32394ef639aae79871df6caf7fffc61d54f7bbcacbb153`.

Les portées exactes sont `¬(p→q)→(¬p→q)`, `¬(p→q)→(p→¬q)`,
`¬(p→q)→(¬p→¬q)` et `¬(p→q)→(q→p)`. Les trois premières sont les instances
imprimées de ✱2·47–49; ✱2·521 compose ✱2·52 et ✱2·17.

Wikisource commet une erreur numérique certaine en ✱2·52: `p⊃¬q` au lieu de
`¬p⊃¬q`, lecture nette du scan et de Gutenberg. Classification
`digital-witness-error`, jamais `sic`. Aucun défaut de l'imprimé. Confiance haute.
