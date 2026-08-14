# Q331 — ✱21·082, ✱21·083, and ✱21·1 audit

The canonical witness is first-edition volume I, scan leaf 237, printed page
215 (SHA-256 `3124660487bd0c3198c6eb364bba34b6ed62fb6a5946966dd6aae03932b50d0c`).

The Lean representation retains both object carriers of every relation:
`TypedRelation α β := α → β → Prop`. A class of relations is a predicate on
that typed relation space. ✱21·082 and ✱21·083 are exact definition-in-use
reductions: the former preserves the existential predicative matrix and its
formal `R` equivalence; the latter reduces membership to application.

For ✱21·1, `RelationAbstractionApplication` is the exact ✱21·01 definiens.
The theorem retains the existential `φ`, both formal object variables, their
pointwise equivalence with `ψ`, and the continuation `f φ`. Its proof is the
printed definitional expansion (✱4·2 applied to ✱21·01), hence reflexive.

No total relation-class choice object, untyped relation, axiom declaration,
classical principle, inhabitance premise, placeholder, or unsafe escape hatch
is introduced.

## Definition reuse and derivation gate

The next-wave audit preserves ·082 and ·083 as definitions only. Both reduce
genuine named operations (`RelationClassApplication` and
`AbstractRelationClass`) and introduce no proof constructor. They are
axiom-free and do not import or reference the archived `Support` prototype.

The earlier acceptance of ·1 is withdrawn. Although its host proposition has
the right semantic expansion, the Lean proof is `rfl`; there is no relational
object formula, no inductive judgment, and no chain consuming the printed
✱4·2 and ✱21·01 evidence. A `Df` is not licensed as a derivation constructor,
and the archived `Support` cannot be reused to manufacture that chain. Item ·1
therefore remains blocked pending a real object syntax and a derivation from
the earlier theorem/rule infrastructure.

The dependency graphs were rebuilt independently. Definitions ·082 and ·083
are uncited and their reduction bodies call no numbered theorem, so all three
graphs are empty. For ·1 the printed and normalized graphs are exactly
`PM1:✱4·2` and `PM1:✱21·01`; the Lean derivation graph is empty because `rfl`
calls neither. The previous historical-relaxation record is removed: absence
of the printed derivation is a blocker, not a permissible relaxation.
