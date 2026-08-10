# Audit Q208 — PM I, ✱2·3, ✱2·31, ✱2·32

Verdict: **A (résultat Aristotle accepté, en attente de CI)**.

Archive immuable: `aristotle/results/Q208-final.tar.gz`, SHA-256
`f530a04800377e29ec1121638fcf392faa9b143b98dcaddab155f80ec88ab8af`.
Projet `194ae313-ff77-4514-88b8-4262e4f0ee29`, tâche
`bbd8c638-d7a3-4bdd-bb3e-e618a2d70983` (`COMPLETE`).

Sources: première édition, vol. I (1910), pp. 109–110, feuilles 131–132.

- ✱2·3: `Perm q r`, élevé par `Sum p`.
- ✱2·31: ✱2·3, `Assoc p r q`, `Perm r (p∨q)`.
- ✱2·32: `Perm (p∨q) r`, `Assoc r p q`, ✱2·3 `p r q`.

Chaque sorite doit être développé avec ✱2·05 et `detach`; aucun compositeur
postulé. Q208 est une dépendance obligatoire de Q210. Aucun `[sic]` imprimé
n'est établi. Confiance élevée.

Le fichier autonome rendu couvre exactement les trois propositions annoncées.
Il ne contient ni `sorry`, ni `admit`, ni nouvel axiome, ni `unsafe`, ni
sémantique, ni `Classical`, ni compositeur générique. Les corps de preuve
conservent les trois chaînes historiques dans leur ordre; les seules constantes
non primitives sont ✱2·03 et `PM.Derivation.detach`. La mention de `propext`
dans le résumé Aristotle concerne uniquement le `simp` du pont `detach` fourni
dans le prompt, non une dépendance ajoutée par les trois preuves. La version
intégrée attend la certification du noyau Lean 4.30.0 par GitHub Actions; aucune
compilation Lean locale n'a été effectuée.
