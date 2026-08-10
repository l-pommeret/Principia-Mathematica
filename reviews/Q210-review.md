# Audit Q210 — PM I, ✱2·4, ✱2·42, ✱2·43

Verdict: **A (préparation conditionnelle)**. Ne pas soumettre avant intégration
et certification noyau GitHub CI de Q208 **et** Q209.

Source: première édition, vol. I (1910), p. 111, feuille 133.

- ✱2·4 dépend exactement de ✱2·31, Taut et ✱2·38.
- ✱2·42 est `✱2·4 ∼p/p`.
- ✱2·43 est uniquement la lecture définitionnelle de ✱2·42 par ✱1·01.

Le prompt doit être actualisé avec les corps kernel-checkés exacts de Q208 et
Q209 avant soumission, puis son empreinte enregistrée. Aucun `[sic]` imprimé
n'est établi. Confiance élevée sur texte, AST et dépendances; non soumis.

✱2·33 est volontairement exclu: c'est une définition éditoriale de portée,
`p ∨ q ∨ r := (p ∨ q) ∨ r`, à traiter séparément. Elle entre en tension avec
l'actuelle notation Lean `infixr` et interdit de présenter une chaîne nue
associée à droite comme fidèle à PM.
