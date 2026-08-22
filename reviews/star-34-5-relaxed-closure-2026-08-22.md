# ✱34·5 — une définition citée en print, dépliée dans la preuve

22 août 2026.

## L'écart

    ✱34·5.  ⊢ : xR²y . ≡ . (∃z). xRz . zRy      [✱34·1 . (✱34·02)]

La page cite deux choses : la proposition ✱34·1, et — entre parenthèses, selon
la convention des *Principia* pour une définition — le `Df` ✱34·02.

Le terme de preuve Lean n'emploie que ✱34·1. ✱34·02 n'y apparaît pas comme
dépendance parce que la définition est **dépliée définitionnellement** : le
carré relationnel `R²` *est* son expansion, et rien dans le terme n'a à citer
la définition pour l'utiliser.

L'écart est donc entièrement du côté « imprimé mais inutilisé », jamais en
ajout. La preuve n'emploie rien que la page ne cite.

## Ce qui a été fait, et ce qui ne l'a pas été

Aucune tentative de resserrement n'a été menée : il n'y a rien à resserrer. Une
citation de définition n'a pas d'équivalent dans un terme de preuve où la
définition est transparente. Le rendre visible exigerait de rendre ✱34·02
opaque, ce qui changerait l'encodage de tout ✱34 pour une question de
comptabilité.

Le même motif vaudra pour toute proposition dont la page cite un `Df` entre
parenthèses. Il n'est pas propre à ✱34·5.

## Contexte

Cet item n'était visible ni de l'audit ni de personne jusqu'au 22 août 2026,
pour une raison qui n'a rien à voir avec l'écart ci-dessus : sa liaison
d'hypothèse déclarait un type Lean élidé — `Star21EliminationHypothesis
vocabulary (star_34_02 ...) x y`, avec des points de suspension littéraux —
qu'aucun registre ne pouvait reconnaître. Douze autres liaisons de ✱23, ✱33,
✱34 et ✱35 étaient dans le même cas, et leur dépendance à l'axiome de
réductibilité échappait donc entièrement au contrôle. Voir
`metadata/assumptions.json` et la tâche #39.
