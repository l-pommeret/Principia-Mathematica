# Audit Q207 — PM I, ✱2·25–✱2·27

Verdict: **A (préparation seulement)**. Soumettre seulement après CI noyau de
la chaîne canonique jusqu'à ✱2·18.

Source: première édition, vol. I (1910), p. 109, feuille 131. La portée
critique de ✱2·25 est `p ∨ ((p ∨ q) ⊃ q)`, et non
`(p ∨ (p ∨ q)) ⊃ q`. Elle est confirmée à la fois par la ponctuation de
portée et par la démonstration `✱2·1; Assoc`.

✱2·26 est la substitution imprimée `∼p/p`; ✱2·27 est sa lecture par ✱1·01.
Le prompt interdit donc toute règle moderne d'explosion ou de contraction.
Aucun `[sic]` de l'imprimé n'est requis. Confiance élevée; non soumis.

## Audit du résultat Aristotle

Projet `c3989850-3990-469a-927a-b6545449a32a`, tâche
`b284384f-6d02-4b7d-a112-f3ef57fbefc6`, état terminal `COMPLETE`. L'archive
immuable `aristotle/results/Q207-final.tar.gz` porte le SHA-256
`1aa70d025472c3bff7ec1e22b1a3e90c988fb5117a2c015c033c0ad9ad3bd52f`.

Couverture acceptée: les trois cibles exactes ✱2·25–✱2·27. L'AST critique
de ✱2·25 reste `p ∨ ((p ∨ q) ⊃ q)`; sa preuve suit ✱2·1 puis Assoc.
✱2·26 est l'instance imprimée `∼p/p`, et ✱2·27 est sa lecture définitionnelle,
sans inférence ajoutée. Le fichier cible ne contient ni `sorry`, `admit`, nouvel
axiome, `unsafe`, `Classical`, `by_cases`, sémantique, automatisation, ni
substitution générique. Le `Main.lean` du harnais Aristotle n'est pas importé.

Les dépendances directes historique/Lean/normalisées sont concordantes et
consignées dans `metadata/items/PM1-star-2-Q207.json`; `detach` se normalise
vers ✱1·11. Verdict: **A, awaiting-ci**.
