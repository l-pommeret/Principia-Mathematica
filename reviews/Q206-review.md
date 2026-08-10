# Audit Q206 — PM I, ✱2·2, ✱2·21, ✱2·24

Verdict: **A (préparation seulement)**. Énoncés, portées, substitutions et
graphe formel audités; soumission interdite avant certification noyau GitHub
CI de la chaîne canonique jusqu'à ✱2·18.

Sources: première édition, vol. I (1910), pp. 108–109, feuilles 130–131 du
fac-similé Wikisource. PG78050 est seulement un témoin de travail.

- ✱2·2 a pour AST `p ⊃ (p ∨ q)` et conserve `Add; Perm; Syll`.
- ✱2·21 est l'instance `✱2·2 ∼p/p`, sans principe d'explosion ajouté.
- ✱2·24 est `✱2·21.Comm`: ✱2·04 est instancié puis détaché.

Les trois corps exigent uniquement les primitives, ✱2·04/05 et le lemme
métalinguistique prouvé `detach`. Aucun `[sic]` de l'imprimé n'est établi dans
ce lot. Confiance élevée; statut Aristotle: `prepared`, non soumis.

## Audit du résultat Aristotle

Projet `bfb67779-55fc-46b6-acf9-71b88077080a`, tâche
`a67c6b39-8b4a-4fe4-aa2f-a5fd603c681d`, état terminal `COMPLETE`. L'archive
immuable `aristotle/results/Q206-final.tar.gz` porte le SHA-256
`3ffd141774c506e5c962778e83a36448330b773999314323e4c292f5033dd6d7`.

Couverture acceptée: les trois cibles exactes ✱2·2, ✱2·21 et ✱2·24. La
première preuve conserve `Add; Perm; Syll`; la seconde est littéralement
l'instance imprimée de ✱2·2; la troisième applique `Comm` au résultat exact
✱2·21. Le fichier cible n'emploie ni `sorry`, `admit`, nouvel axiome,
`unsafe`, `Classical`, `by_cases`, sémantique, automatisation, ni substitution
générique. Le `Main.lean` du harnais Aristotle n'est pas importé.

Les dépendances Lean directes se normalisent exactement vers les références
PM consignées dans `metadata/items/PM1-star-2-Q206.json`; `detach` réalise
✱1·11 dans le contexte de variables réelles. Verdict: **A, awaiting-ci**.
