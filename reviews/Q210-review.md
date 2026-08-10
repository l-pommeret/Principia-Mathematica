# Audit Q210 — PM I, ✱2·4, ✱2·42, ✱2·43

Verdict: **A (réponse Aristotle acceptée, en attente de CI)**. L'archive
immuable `aristotle/results/Q210-final.tar.gz` a l'empreinte SHA-256
`4f0d59f1f63a2c8960d9de45adb264200bc8ef62310309b41bee106e8f36739a`.
Elle contient exactement les trois cibles ✱2·4, ✱2·42 et ✱2·43, sans
modification de leurs énoncés.

Source: première édition, vol. I (1910), p. 111, feuille 133.

- ✱2·4 dépend exactement de ✱2·31, Taut et ✱2·38.
- ✱2·42 est `✱2·4 ∼p/p`.
- ✱2·43 est uniquement la lecture définitionnelle de ✱2·42 par ✱1·01.

Les corps intégrés emploient les déclarations Q208/Q209 déjà kernel-checkées
du dépôt, et non les copies autonomes réparées par Aristotle. Aucun `[sic]`
imprimé n'est établi. Confiance élevée sur texte, AST et dépendances.

Audit formel: aucun `sorry`, `admit`, `unsafe`, nouvel axiome, appel à
`Classical`, substitution générique ou preuve sémantique. ✱2·4 expose
successivement ✱2·31, Taut, ✱2·38 et la composition Syll.; ✱2·42 est
strictement l'instance `∼p/p`; ✱2·43 n'ajoute que la lecture définitionnelle
✱1·01. Les dépendances sont consignées dans
`metadata/items/PM1-star-2-Q210.json`.

L'archive autonome d'Aristotle utilise Lean 4.28.0 malgré la demande 4.30.0;
elle constitue une réponse à auditer, non une certification du dépôt. Seule
la prochaine CI GitHub épinglée à Lean 4.30.0 pourra établir le statut
`kernel-checked`.

✱2·33 est volontairement exclu: c'est une définition éditoriale de portée,
`p ∨ q ∨ r := (p ∨ q) ∨ r`, à traiter séparément. Elle entre en tension avec
l'actuelle notation Lean `infixr` et interdit de présenter une chaîne nue
associée à droite comme fidèle à PM.
