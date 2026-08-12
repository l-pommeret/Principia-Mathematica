# Q297 review

**Source collated; all five Q297 items kernel represented.** Leaves 204–205
(pp. 182–183), scan hashes
`23427375b6f708a53ed91a28fb43eed247d732ff4047ee7e88fd779e2a50ad28`
and `1a8f4bf7870135c6f7047f5f5b6a6ac1fe416f327c28b59766fce3711c3e1a7c`,
plus PG 78050, witness these forms.

The exact reductions ✱14·02/·03/·04 are represented, without term-level
descriptions, in `DescriptionDefinitions` and exposed by the source module.

`Star14Q297Kernel.lean` closes the former assertion-layer gap for ✱14·18 and
✱14·21 by retaining Russell's contextual analysis. `DescriptionExists φ` is
literally `∃ b, ∀ x, φ x ↔ x = b`; `DescriptionApplies φ ψ` adds `ψ b` to
that same witness. Thus ✱14·18 introduces the contextual witness from
existence and universal `ψ`, while ✱14·21 projects the witness back out.
No description is made into a total term, no choice principle or nonempty
carrier is assumed, and no `sorry`, new axiom, or generic detachment rule is
used.

Targeted verification with Lean 4.30.0:

```text
lake env lean Principia/Architecture/Star14Q297Kernel.lean
```
