# Q299 review

Leaf 206 (p. 184), SHA-256 `d82a452d1485876e6962c1ff219a9304404d429a85cd20e1bdebfdc1db47b3f8`, and PG 78050 collate all five loci. The printed proofs use scoped contextual descriptions, existence/identity equivalences, and a two-description function form. `DescriptionSyntax` provides syntax and expansion only, so this is source-only and architecture-gated; no Lean target is licensed.

The post-Q310 audit is more precise. ✱14·1/·101 require an asserted
object-language equivalence between a `descriptionScope` formula and its
existential definiens; meta-level equality of their syntax trees is not that
proposition. ✱14·11 similarly requires asserted equivalence for
`descriptionExists`. ✱14·111/·112 can reuse the nested de Bruijn scopes now
provided by `descriptionScopePair`, but still require a two-candidate
assertion and the printed equivalence rules. Thus the exact missing boundary
is a `DescriptionDerivation : Formula … → Prop` rule family, not more scope
syntax. No target is licensed until that family is source-audited.
