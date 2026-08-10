# Audit Q200 — détachement métalinguistique dans le calcul élémentaire de PM

Verdict: **A — cible fidèle aux deux règles primitives d'inférence de PM**.

Sources canoniques: Whitehead et Russell, *Principia Mathematica*, première
édition, volume I (1910), ✱1·1 et ✱1·11, pp. 98–99:

- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/120
- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/121

## Statut de la déclaration

`PM.Derivation.detach` n'est ni une proposition objet, ni un nouveau principe
primitif attribué à PM. C'est un lemme métalinguistique rendu nécessaire par
l'indexation explicite du jugement Lean par un contexte de variables réelles.
Il sélectionne l'une des deux règles primitives déjà présentes:

- si `Γ = []`, le jugement porte sur une proposition élémentaire définie et le
  détachement est exactement ✱1·1;
- si `Γ = τ :: Δ`, le jugement porte sur une fonction propositionnelle à une
  ou plusieurs variables réelles et le détachement est exactement ✱1·11.

L'analyse de `Γ` ne raisonne pas sur la vérité des formules. Elle ne fait que
rendre explicite la distinction syntaxique et métalinguistique faite par PM
entre l'assertion d'une proposition définie et celle d'une fonction
propositionnelle contenant des variables réelles.

## Cible exacte

```lean
namespace PM.Derivation

theorem detach {Γ : PM.RealContext} {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hφψ : PM.Derivation (φ ⊃ₚ ψ)) :
    PM.Derivation ψ := by
  -- analyse de Γ seulement

end PM.Derivation
```

Dans la branche non vide, la preuve requise par le constructeur ✱1·11 est
uniquement `τ :: Δ ≠ []`, conséquence structurelle de la forme du contexte.
Elle ne constitue pas une hypothèse logique ajoutée à la dérivation.

## Nécessité formelle

Le calcul actuel rend correctement les domaines des deux règles disjoints:
`star_1_1` est limité à `Elementary []`, tandis que `star_1_11` accepte
`Elementary Γ` sous la preuve `Γ ≠ []`. Les théorèmes dérivés sont cependant
présentés uniformément pour un contexte arbitraire `{Γ}`. Une invocation
uniforme de l'un ou l'autre constructeur serait donc incorrecte:

- employer seulement ✱1·1 effacerait la distinction des variables réelles;
- employer seulement ✱1·11 serait impossible pour `Γ = []` et assimilerait à
  tort les propositions définies aux fonctions propositionnelles.

Le découpage exhaustif `[] | τ :: Δ` est ainsi la seule couche d'adaptation
requise entre ces règles historiques et l'interface générique des théorèmes.

## Exclusions auditées

La preuve ne doit introduire aucun modus ponens moderne indépendant, aucune
interprétation de `Elementary` dans `Prop`, aucune sémantique, aucun principe
classique, aucune substitution objet et aucun nouvel axiome. Elle ne doit pas
modifier `Derivation`, relâcher la condition de ✱1·11, ni confondre le contexte
de variables réelles avec une liste d'hypothèses logiques.

Ce lemme pourra être cité dans les formalisations ultérieures comme
l'explicitation Lean de l'emploi de ✱1·1 ou ✱1·11. L'audit d'une preuve devra
toujours conserver la référence PM particulière imprimée dans sa
démonstration.

Confiance: élevée pour la correspondance entre les deux branches et les deux
règles primitives. Aucune proposition historique nouvelle n'est revendiquée.

## Audit du résultat Aristotle

Archive immuable: `aristotle/results/Q200-final.tar.gz`
SHA-256: `a161ad56cfde7764e72c21bcc2dd72318861ea421ffe51230867aafdd16f39cd`

Verdict du résultat: **complet, en attente de CI du dépôt**.

La déclaration livrée conserve exactement les paramètres dépendants, les deux
hypothèses explicites et la conclusion demandés. Son unique analyse porte sur
la forme de `Γ`:

- la branche `[]` appelle seulement `PM.Derivation.star_1_1`;
- la branche `τ :: Δ` appelle seulement `PM.Derivation.star_1_11`, avec
  `List.cons_ne_nil τ Δ` comme seule preuve structurelle supplémentaire.

Le fichier de preuve `RequestProject/Q200.lean` ne contient ni `Classical`, ni
`by_cases`, ni nouvel axiome, ni `sorry`, `admit` ou déclaration `unsafe`. Le
`open scoped Classical` trouvé dans le fichier générique
`RequestProject/Main.lean` de l'archive n'est pas importé par la preuve Q200 et
n'entre pas dans la déclaration intégrée. La vérification kernel définitive de
l'intégration est réservée à GitHub Actions, conformément à la politique du
projet; aucune compilation Lean locale n'a été exécutée pendant cet audit.
