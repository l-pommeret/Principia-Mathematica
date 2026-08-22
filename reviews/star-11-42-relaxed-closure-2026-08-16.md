# ✱11·42 — clôture relâchée, et la tentative stricte qui l'a précédée

16 août 2026.

## Ce que PM imprime

    ✱11·42.  [✱10·5]

Une seule citation. Notre démonstration Lean en emploie six :

    ✱1·11   ✱3·26   ✱4·11   ✱10·5   ✱10·11   ✱10·271

Aucune proposition imprimée n'est inutilisée : ✱10·5 sert. L'écart est donc
entièrement en ajout, jamais en retrait.

## La tentative stricte, et pourquoi elle a échoué

Le défaut a été découvert par ricochet. L'audit de dépendances venait d'être
élargi au palier `awaiting-ci` pour une tout autre raison — briser un amorçage
circulaire sur la frontière `kernel-checked` — et il a signalé :

    PM1:✱11·42: unindexed qualified Lean reference Star10For11.star_10_5

Le `star_10_5` employé n'était pas le ✱10·5 catalogué mais un homonyme : une
re-démonstration indépendante de 96 lignes vivant dans le namespace local
`PM.RamifiedSyntax.Star10For11`, passant par `star_11_11_saturated`, et ne
dérivant jamais de la proposition cataloguée. Le gate `verify_printed_citations`
cherchait le NOM `star_10_5` dans le terme de preuve ; il le trouvait, et
déclarait la route imprimée suivie. **Un homonyme suffisait à le satisfaire.**

L'hypothèse de travail était la même que treize fois ce jour-là : le sosie
existe parce que la proposition cataloguée est écrite trop étroitement. Un agent
a donc généralisé `PM.RamifiedSyntax.star_10_5` sur l'ordre matriciel — treize
zéros littéraux supprimés, aucun restant, fichier compilé, axiomes vides.

**Cela n'a pas suffi, et pour une raison qui n'est pas l'ordre.** ✱10·5 lie une
matrice sur UNE variable apparente, `Formula … [sort] B` ; ✱11·42 lui en fournit
DEUX, `Formula … [sort, sort] B`. L'obstacle est l'arité, pas l'ordre. Le
paramétrer demanderait de généraliser ✱10·5 sur le contexte de variables
apparentes lui-même, ce qui touche la forme des matrices et non un entier, et
dont la portée dépasse ✱11·42.

La généralisation sur l'ordre a été conservée : elle est juste, et utile
ailleurs. Le sosie subsiste, désormais déclaré dans `lean_realizations` comme
réalisant ✱10·5 à l'arité 2 — décision éditoriale du mainteneur, prise en
connaissance de l'alternative.

## Les cinq ajouts

| ajout | pourquoi la formalisation l'exige |
|---|---|
| ✱1·11 | détachement en contexte de variables réelles ; `Star11Derived` déclare `variable {real : Context}`, donc le contexte est arbitraire et non vide |
| ✱3·26 | projection d'un produit, employée pointwise sous les deux binders |
| ✱4·11 | congruence d'équivalence sous la négation |
| ✱10·11 | généralisation d'une matrice sous le quantificateur |
| ✱10·271 | transport d'une équivalence formelle sous l'universelle |

Ce sont les pas que PM laisse implicites dans un `Dem.` de deux lignes et
qu'une vérification par machine doit écrire. Aucun n'introduit de contenu
étranger au tome I : les cinq sont eux-mêmes des propositions cataloguées et
démontrées.

## Ce qui reste à faire

La bonne correction reste la généralisation de ✱10·5 sur l'arité, qui rendrait
le sosie inutile et ramènerait ✱11·42 à une clôture stricte. Elle est consignée
en tâche #39 avec les six autres théorèmes portant un numéro des PM hors du
namespace canonique.
