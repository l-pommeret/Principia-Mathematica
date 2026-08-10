# Audit Q211 — PM I, ✱2·45–✱2·49

Verdict: **A — réponse Aristotle acceptée et intégration kernel-checkée**.
Le commit immuable
`d41b8a34bdcaad43e4f753e775a7bd2c79b45add` a passé le step GitHub Actions
« Build and kernel-check the edition » du run
`https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31422968106`.
L'archive
immuable `aristotle/results/Q211-final.tar.gz` a l'empreinte SHA-256
`fb9130274bfcecd6ec20b2f10f920e7dec83ad6e8531ab75e66a029ec1f1e026`.
Elle contient exactement les cinq cibles ✱2·45–✱2·49, sans modification de
leurs énoncés. Texte, AST et graphe ont été audités contre l'imprimé.

Sources canoniques: première édition, vol. I, pp. 111–112, feuilles 133–134.
SHA-256 des JPEG Wikimedia 1920 px: feuille 133
`0c0df442a2217662c826153ecfdc29819292ab889831fa82d930bd42754ce7b5`;
feuille 134
`3818c499d4043461da32394ef639aae79871df6caf7fffc61d54f7bbcacbb153`.

Portées: `¬(p∨q)→¬p`, `¬(p∨q)→¬q`, `¬(p∨q)→(¬p∨q)`,
`¬(p∨q)→(p∨¬q)`, `¬(p∨q)→(¬p∨¬q)`. Les deux premières emploient les
formes prouvées de Transp.; les trois suivantes sont les Syll. imprimés.
`Transp` et `Syll` ne sont pas de nouveaux constructeurs. Aucun défaut de
l'imprimé ni divergence substantielle des témoins n'est établi. Confiance haute.

Audit formel: cinq cibles et seulement cinq, ✱2·45–✱2·49. Les corps intégrés
emploient les déclarations Q205/Q206 déjà kernel-checkées du dépôt, et non des
axiomes ni les copies autonomes de l'archive. ✱2·45 et ✱2·46 utilisent
exactement Transp. (✱2·16); ✱2·47–✱2·49 développent chacun le Syll. imprimé
par ✱2·05 et `detach`. Les substitutions imprimées restent des instanciations
de paramètres Lean, sans règle générique ajoutée.

Aucun `sorry`, `admit`, `unsafe`, nouvel axiome, appel à `Classical`, preuve
sémantique ou cible supplémentaire n'apparaît dans le fichier de réponse.
La notation `∨ₚ` associe à gauche conformément à ✱2·33 et `detach` conserve
la distinction métalinguistique entre ✱1·1 et ✱1·11. Les dépendances exactes
sont consignées dans `metadata/items/PM1-star-2-Q211.json`.

L'archive autonome d'Aristotle utilise Lean 4.28.0 malgré la demande 4.30.0;
elle est donc une réponse à auditer, non une certification du dépôt. La
certification finale est celle du lot intégré, vérifié par GitHub CI avec la
version Lean épinglée du dépôt.
