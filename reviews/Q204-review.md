# Audit Q204 — PM I, ✱2·11–✱2·14

Verdict: **A (préparation seulement) — texte, portées, dépendances et
cibles formelles audités; soumettre seulement après certification noyau de
Q200 et Q203**.

Sources canoniques: Whitehead et Russell, *Principia Mathematica*, première
édition, volume I (1910), pp. 105–106, feuilles de scan 127–128:

- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/127
- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/128

Témoin de travail indépendant: Project Gutenberg ebook 78050. Le fac-similé
fait autorité. Les dérivés JPEG contrôlés ont respectivement les SHA-256
`353904a9208e3b27ec48340eeb42a809f770c99e797ddd1f4d306c7da7df29fb` et
`50de3f3d318f242e51c387be84eba8cd18ae271884bcc412b4afc7dfabeb2cb2`.

## Couverture diplomatique

```text
✱2·11.  ⊢ . p ∨ ∼p

Dem.

        [Perm  ∼p, p/p, q]  ⊢ : ∼p ∨ p . ⊃ . p ∨ ∼p       (1)
        [(1).✱2·1.✱1·11]  ⊢ . p ∨ ∼p
```

Le texte qui suit est: `This is the law of excluded middle.`

```text
✱2·12.  ⊢ . p ⊃ ∼(∼p)

Dem.

        [✱2·11  ∼p/p]  ⊢ . ∼p ∨ ∼(∼p)       (1)
        [(1).(✱1·01)]  ⊢ . p ⊃ ∼(∼p)

✱2·13.  ⊢ . p ∨ ∼{∼(∼p)}
```

Le texte intermédiaire est: `This proposition is a lemma for ✱2·14, which,
with ✱2·12, constitutes the principle of double negation.`

```text
Dem.

        [Sum  ∼p, ∼{∼(∼p)}/q, r]
          ⊢ :. ∼p . ⊃ . ∼{∼(∼p)} : ⊃ :
               p ∨ ∼p . ⊃ . p ∨ ∼{∼(∼p)}       (1)
        [✱2·12  ∼p/p]  ⊢ : ∼p . ⊃ . ∼{∼(∼p)}       (2)
        [(1).(2).✱1·11]
          ⊢ : p ∨ ∼p . ⊃ . p ∨ ∼{∼(∼p)}       (3)
        [(3).✱2·11.✱1·11]  ⊢ : p ∨ ∼{∼(∼p)}

✱2·14.  ⊢ . ∼(∼p) ⊃ p

Dem.

        [Perm  ∼{∼(∼p)}/q]
          ⊢ : p ∨ ∼{∼(∼p)} . ⊃ . ∼{∼(∼p)} ∨ p       (1)
        [(1).✱2·13.✱1·11]  ⊢ : ∼{∼(∼p)} ∨ p       (2)
        [(2).(✱1·01)]  ⊢ : ∼(∼p) ⊃ p
```

La linéarisation des fractions est `remplacements/variables`; elle conserve
l'ordre du scan. La typographie exacte des accolades sert seulement à rendre
non ambiguë l'itération de la négation et se traduit par des parenthèses dans
la cible Lean.

## Divergence du témoin Gutenberg

Dans la première ligne de la démonstration de ✱2·13, le `data-tex` Project
Gutenberg concatène les deux remplacements de la fraction de Sum:
`∼p∼{∼(∼p)}`. Le scan les sépare bien: le numérateur contient deux
expressions, `∼p` et `∼{∼(∼p)}`, correspondant à `q` et `r`. Il s'agit
d'une erreur du témoin numérique, non d'un *sic* de l'édition imprimée. La
virgule de la transcription diplomatique ci-dessus est donc une restitution
du scan, pas une correction de Whitehead et Russell.

Aucun `sic`, `corr.` ou `conj.` relatif à l'imprimé n'est requis pour ce lot.

## Portées et cibles Lean

- ✱2·11: `p ∨ ∼p`.
- ✱2·12: `p ⊃ ∼(∼p)`.
- ✱2·13: `p ∨ ∼(∼(∼p))`.
- ✱2·14: `∼(∼p) ⊃ p`.

Le nombre de négations est critique: ✱2·13 a trois négations dans son
second disjoint; la ligne Perm de ✱2·14 permute `p` et ce même terme à trois
négations. Par ✱1·01, `∼(∼p) ⊃ p` se développe exactement en
`∼{∼(∼p)} ∨ p`.

## Dépendances et reconstruction historique

Ordre interne obligatoire: ✱2·11, ✱2·12, ✱2·13, ✱2·14.

- ✱2·11 instancie Perm (✱1·4) avec `p ↦ ∼p`, `q ↦ p`, puis
  détache ✱2·1.
- ✱2·12 instancie ✱2·11 avec `p ↦ ∼p`; la cible est seulement sa
  lecture par la définition ✱1·01.
- ✱2·13 instancie Sum (✱1·6) avec le paramètre de contexte `p` inchangé,
  `q ↦ ∼p`, `r ↦ ∼(∼(∼p))`; il détache ensuite ✱2·12 instancié par
  `∼p`, puis ✱2·11.
- ✱2·14 instancie Perm avec `p ↦ p`, `q ↦ ∼(∼(∼p))`, détache
  ✱2·13, puis change seulement la notation selon ✱1·01.

Chaque emploi imprimé de ✱1·11 est représenté par le lemme métalinguistique
prouvé `PM.Derivation.detach`, qui choisit ✱1·1 dans le contexte vide et
✱1·11 dans un contexte réel non vide. Aucun modus ponens objet générique
n'est ajouté.

## Porte de soumission

Q204 est **prepared**, non **submitted**. Le prompt reproduit avec leurs corps
les résultats antérieurs nécessaires pour ne pas demander à Aristotle de les
croire comme axiomes. Dans le dépôt canonique, la soumission reste conditionnée
à l'intégration et à la certification GitHub CI de Q200 et Q203, ainsi qu'au
contrôle d'absence de `sorry`, `admit`, `unsafe` ou axiome ajouté.

Confiance: élevée pour les formules, les portées, le nombre de négations et le
graphe de dépendances, sur inspection des deux dérivés canoniques identifiés
ci-dessus et collation avec le témoin Gutenberg.

## Audit du résultat Aristotle

Verdict du résultat: **A — accepté pour intégration, en attente de GitHub CI**.

- projet: `a5ae3859-2a76-49aa-8200-b893afdd539a`;
- tâche terminale: `16e2d599-50fc-4908-818a-7cd46f1ba7e9` (`COMPLETE`);
- archive immuable: `aristotle/results/Q204-final.tar.gz`;
- SHA-256: `4e2893472492ddf637083af934a3e1cf1796dbd2334b6113bd25e55442af8554`.

L'archive contient exactement les quatre déclarations demandées, dans l'ordre
✱2·11–✱2·14 et avec les cibles auditées ci-dessus. Le fichier formel ne
contient aucun `sorry`, `admit`, `axiom`, `unsafe`, emploi de `Classical`, ni
raisonnement sémantique. Les corps suivent les démonstrations imprimées:
Perm puis ✱2·1 pour ✱2·11; instance de ✱2·11 et ✱1·01 pour ✱2·12; Sum,
✱2·12 et ✱2·11 pour ✱2·13; Perm et ✱2·13 pour ✱2·14. Chaque emploi imprimé
de ✱1·11 est réalisé par `PM.Derivation.detach`. Aucune dépendance logique
postérieure ou non imprimée n'a été introduite.

La compilation annoncée dans l'environnement Aristotle n'est pas la preuve
de publication de cette édition: le statut demeure `awaiting-ci` jusqu'au
succès de la CI GitHub au commit intégrant ce lot.
