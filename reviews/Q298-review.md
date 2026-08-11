# Q298 review

Leaf 205 (p. 183), SHA-256 `1a8f4bf7870135c6f7047f5f5b6a6ac1fe416f327c28b59766fce3711c3e1a7c`, and PG 78050 collate these identity/existence loci. They require contextual existence and identity signatures absent from DescriptionSyntax; source-only, architecture-gated.

Audit against the current API: `Formula.equal` accepts only genuine `Term`s,
so none of ✱14·202/·204/·205/·28/·13 may place a description in either
argument slot. Their future signatures must first eliminate every displayed
description with `descriptionScope`/`descriptionScopePair`, then place the
resulting formula under a metalinguistic judgement of the shape
`DescriptionDerivation (formula : Formula …) : Prop`. That judgement and its
identity/substitution rules do not yet exist. Encoding the displayed equality
as Lean equality, or adding `Term.description`, would fail the gate.
