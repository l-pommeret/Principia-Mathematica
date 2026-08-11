# Gate kernel ✱5·13 — PM I, p. 129

Verdict: **un seul candidat minimal, prêt pour CI distante** :
`PM1:✱5·13`. Le corps de
`Principia/FirstEdition/Volume1/Part1/SectionA/Star5Kernel.lean` applique
✱2·521 à `p,q`, puis ✱2·54 à `(p ⊃ q),(q ⊃ p)`. Il n'emploie aucun axiome,
connectif Lean natif, sémantique, `Classical`, `sorry`, `admit` ou règle de
substitution générale. Les deux branches explicites sont exactement ✱1·1
pour `Γ = []` et ✱1·11 pour `Γ ≠ []`.

La feuille canonique 151 (SHA-256
`8ad683eab8e99f0aab97f8a6b1e0179c28e354a9f678c4df2cd1e2fb2d510f4a`)
imprime `[✱2·521]`, un seul numéro; le précédent découpage
`[✱2·5·21]` venait de la transcription Wikisource. L'application de ✱2·521
ne fournit que `∼(p ⊃ q) ⊃ (q ⊃ p)`. L'emballage en disjonction nécessite
donc l'unique supplément ✱2·54, absent de la citation imprimée; la métadonnée
le déclare comme relaxation, sans corriger le texte PM.

✱5·11 et ✱5·12 ne sont pas promus : sur la feuille 134, ✱2·51 conclut
`p ⊃ ∼q` et ✱2·52 conclut `∼p ⊃ ∼q`, alors que leurs cibles demandent
respectivement `∼p ⊃ q` et `p ⊃ ∼q` avant ✱2·54. Leur problème est une
incompatibilité de citations imprimées, non une simple omission d'inférence.
✱5·14 reste hors de ce lot minimal : sa chaîne `Simp . Transp . ✱2·21`
requiert une reconstruction séparée de ces alias.

Ce statut est volontairement `awaiting-ci` : aucune commande Lean locale n'a
été exécutée. La prochaine action autorisée est le build/kernel-check distant
du seul module `Star5Kernel`; après succès immuable, mettre uniquement
✱5·13 à `kernel-checked` avec le run CI.
