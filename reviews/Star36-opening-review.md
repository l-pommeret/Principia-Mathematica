# Audit sémantique — PM I ✱36, ouverture

La transcription canonique contient les 24 identifiants de ✱36, chacun mappé à
une unique déclaration des trois kernels existants. Le premier lot ·01, ·11,
·13, ·2 et ·201 conserve exactement restriction, appartenance et intersections,
sans hypothèse ajoutée; il est promu `awaiting-ci`.

## Audit strict du deuxième lot

Les cinq cibles ✱36·202, ·203, ·21, ·22 et ·23 sont exactes. Les trois
premières sont des égalités extensionnelles de restriction et d'intersection;
·22 conserve l'inclusion et le témoin intermédiaire de la composition; ·23
conserve exactement la distribution sur l'union. Aucun lemme PM antérieur n'est
appelé directement par les corps Lean, donc les trois graphes sont vides.

## Audit strict du troisième lot

Les cinq cibles ✱36·24, ·241, ·25, ·26 et ·27 sont exactes. Les deux
monotonies conservent leurs hypothèses d'inclusion; ·25 conserve les deux sens de
l'équivalence entre champ inclus et restriction inchangée; ·26 prouve les deux
compositions nulles à partir de la disjonction imprimée; ·27 est l'identité sur
la classe nulle. Aucun refus ni appel direct à un théorème PM antérieur.

## Audit strict du quatrième lot

Les cinq cibles ✱36·28, ·29, ·3, ·31 et ·32 sont exactes. Elles conservent
respectivement la restriction universelle, la caractérisation par le carré,
l'intersection avec le champ, son cas vide et l'invariance sous égalité de ces
intersections. ·32 réemploie directement ·3 (arête et relaxation documentées).
·31 a seulement été déqualifiée syntaxiquement pour rendre ses définitions
locales visibles comme infrastructure; aucun refus sémantique.
