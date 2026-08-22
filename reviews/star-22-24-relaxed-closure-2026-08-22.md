# ✱22 et ✱24 — relevé des clôtures relâchées

22 août 2026.

## Statut de la tentative stricte

Cette revue consigne le graphe extrait des termes Lean existants. Aucune
tentative de resserrement des preuves n'a été menée dans ce chantier, qui est
limité aux métadonnées. Les écarts ci-dessous sont donc constatés et compris,
mais pas encore attaqués par une modification des formalismes ou des preuves.

## Écarts exacts

| item | au-delà de l'imprimé | imprimé mais inutilisé | raison dans la formalisation |
|---|---|---|---|
| ✱22·01 | ✱20·02 | — | L'inclusion est développée en implication pointwise entre deux appartenances. |
| ✱22·02 | ✱20·01, ✱20·02 | — | L'intersection est une abstraction contextuelle de classe dont la matrice emploie l'appartenance. |
| ✱22·03 | ✱20·01, ✱20·02 | — | L'union est une abstraction contextuelle de classe dont la matrice emploie l'appartenance. |
| ✱22·04 | ✱20·01, ✱20·02 | — | Le complément est une abstraction contextuelle de classe sur une appartenance niée. |
| ✱22·05 | ✱20·01, ✱20·02 | — | La différence élimine intersection et complément, puis explicite abstraction et appartenance. |
| ✱22·44 | ✱20·02, ✱22·01 | — | L'instance ramifiée de ✱10·3 développe les appartenances et la définition de l'inclusion. |
| ✱22·441 | ✱20·02 | `Imp` | ✱10·1 est instancié sur les appartenances; `Imp` est réalisé par un auxiliaire propositionnel local. |
| ✱24·01 | ✱13·01, ✱20·01 | — | La classe universelle devient l'abstraction contextuelle de la matrice d'auto-identité. |
| ✱24·02 | ✱13·01, ✱20·01 | — | La classe nulle est entièrement développée en abstraction de la négation de l'auto-identité. |

Les listes reprennent exactement la différence calculée par
`deps_for_item.py`; aucun `printed_dependencies` n'a été modifié.
