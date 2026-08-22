# ✱3–✱5 — audit des clôtures relâchées

22 août 2026.

## Statut de la tentative stricte

Ce chantier est limité aux métadonnées. Aucune preuve Lean n'a été resserrée
et aucune tentative de clôture stricte n'a été menée. Les écarts ci-dessous
sont constatés par l'extracteur de `scripts/verify_dependencies.py`; ils sont
documentés, mais ne sont pas encore attaqués.

## Clôtures extraites

- **✱3·4** — ajouts : ✱1·11, ✱2·05, ✱2·14, ✱2·16 ; imprimés inutilisés :
  ✱1·01, ✱3·01, `Transp`. La preuve développe la transposition, la double
  négation, la composition et le détachement ; les définitions imprimées sont
  absorbées par réécriture.
- **✱3·37** — ajouts : ✱1·11, ✱2·02, ✱2·05, ✱2·16, ✱2·77, ✱3·3,
  ✱3·31 ; imprimés inutilisés : `Exp`, `Imp`, `Syll`, `Transp`. Le terme Lean
  remplace ces quatre instructions métalinguistiques par les propositions
  cataloguées qui réalisent leurs étapes.
- **✱3·41** — ajouts : ✱1·11, ✱2·06 ; imprimé inutilisé : `Syll`. La
  syllogistique est explicitée par ✱2·06 puis appliquée par détachement.
- **✱3·42** — ajouts : ✱1·11, ✱2·06 ; imprimé inutilisé : `Syll`. La même
  expansion explicite s'applique à la prémisse ✱3·27.
- **✱3·43** — ajouts : ✱1·11, ✱2·05, ✱3·31 ; imprimés inutilisés : `Imp`,
  `Syll`. La composition et l'importation sont des arêtes explicites du terme.
- **✱4·36** — ajouts : ✱2·02, ✱2·08, ✱3·26, ✱3·27 ; imprimé inutilisé :
  `Fact`. La convention `Fact` est développée en implication, identité et
  projections du produit ; ✱3·47 demeure utilisée.
- **✱4·78** — ajouts : ✱1·11, ✱3·2, ✱3·26, ✱4·21 ; imprimé inutilisé :
  ✱1·01. Le terme rend explicites détachement, empaquetage d'équivalence,
  congruence et transitivité, tandis que ✱1·01 se réduit définitionnellement.
- **✱5·22** — ajouts : ✱1·1, ✱1·11, ✱3·2, ✱4·22 ; imprimé inutilisé :
  ✱4·51. Le terme courant empaquette et compose les équivalences dans les deux
  cas de contexte sans appeler directement ✱4·51.

Pour ✱3·4, ✱3·37, ✱3·41, ✱3·42, ✱3·43 et ✱4·78, les déclarations Lean
quantifient un contexte élémentaire arbitraire `{Γ}`. Le `detach` extrait est
donc résolu vers ✱1·11, conformément aux précédents ✱2·06 et ✱2·08, et non vers
la règle de contexte vide ✱1·1.
