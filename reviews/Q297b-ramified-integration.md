# Q297b — intégration ramifiée de ✱14·21

La tentative stricte part de la chaîne imprimée `✱14·1`, `✱10·5`,
`✱14·11`.  Dans `PM.RamifiedSyntax`, les deux propositions de ✱14 certifient
les expansions contextuelles, tandis que ✱10·5 n'avait pas encore de déclaration
publique indexée dans `Star10Derived.lean`.

La déclaration `star_14_21` reconstruit donc localement ce seul pas : ✱3·26
projette la matrice d'unicité, ✱9·1 introduit son existentiel, le `Syll`
à ordres indépendants compose les implications, puis la généralisation et
✱10·23 rendent à l'antécédent existentiel sa portée imprimée.  Le candidat de
la description reste lié dans la matrice ; aucun terme descriptif n'est créé.

La relaxation ne remplace aucune dépendance imprimée par un résultat étranger :
elle note seulement que l'appel direct à ✱10·5 est déplié dans un lemme privé,
donc absent du graphe lexical public.

Pour ✱14·18, la même encapsulation privée est nécessaire afin que les transports
d'ordres calculatoires (`Eq.mp`) ne soient pas pris pour des dépendances historiques.
Le corps privé suit les lignes imprimées : spécialisation ✱10·1, conservation de
la matrice d'unicité par `Fact`, relèvement existentiel correspondant à
✱10·11·28, puis normalisation de portée ✱10·35 et expansions ✱14·1·11.
