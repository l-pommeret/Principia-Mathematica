# Gate noyau des prérequis Q244 — ✱3·43 et ✱4·51

Verdict : **intégrés canoniquement et compilés localement**.

✱3·43 est la construction `Comp` déjà vérifiée dans le module canonique
`Star4Q240.lean`. Elle compose ✱3·2, ✱2·05, ✱2·77, ✱2·06 et ✱3·31 avec les
deux branches explicites de l'inférence primitive.

Pour ✱4·51, l'expansion définitionnelle de ✱3·01 transforme
`∼(p ∧ q) ≡ (∼p ∨ ∼q)` en la réciproque de l'équivalence de double négation
✱4·13 appliquée à `∼p ∨ ∼q`. ✱3·22 échange exactement les deux implications
de cette équivalence. Le corps ne contient ni placeholder, ni nouvel axiome,
ni sémantique, ni connectif Lean natif.
