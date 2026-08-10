# Audit Q211 — PM I, ✱2·45–✱2·49

Verdict: **A — prêt pour soumission**. Texte, AST et graphe audités; Q205,
Q206 et Q210 ainsi que leur clôture de dépendances sont désormais certifiés
par GitHub CI. Le prompt autonome reproduit les véritables corps Lean du
dépôt, sans postuler aucun résultat antérieur.

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

Audit du prompt: cinq cibles et seulement cinq, ✱2·45–✱2·49. Les corps
certifiés de ✱2·03–✱2·08, ✱2·1, ✱2·11, ✱2·12, ✱2·16 et ✱2·2 fournissent une
clôture autonome. La notation `∨ₚ` associe à gauche conformément à ✱2·33 et
`detach` est le corps certifié distinguant ✱1·1 de ✱1·11. Aucun `sorry`,
`admit`, axiome auxiliaire, `unsafe` ou recours à `Classical` n'est fourni.
