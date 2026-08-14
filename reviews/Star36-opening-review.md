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

## Audit strict du cinquième lot

Le dernier catalogue non audité ne contient que quatre cibles, ✱36·33, ·34,
·35 et ·4; il n'existe pas de second catalogue `prepared` dans ✱36. Les quatre
cibles sont exactes et passent à `awaiting-ci`. ·33 conserve l'invariance sous
restriction au champ, ·34 la commutation avec la converse, ·35 l'inclusion du
carré restreint et ·4 l'invariance de l'union sous l'hypothèse de disjonction
imprimée. Les preuves de ·33 et ·35 réemploient directement ·25 et ·22; ces
deux arêtes absentes des lignes imprimées sont enregistrées comme relaxations
de clôture. ·34 et ·4 n'appellent aucun théorème PM antérieur. Aucun item n'est
refusé et aucun doublon n'est créé.
