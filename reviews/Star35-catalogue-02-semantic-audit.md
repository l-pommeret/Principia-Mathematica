# ✱35 catalogue 02 Star2/T1–T9 audit

This audit covers ·1, ·101, ·102, ·103, and ·11. A complete item must provide
the printed formula as an object-language AST, an assertion judgement, and an
axiom-free kernel derivation licensed by the source rules. Predicate-level
`Prop`, support projections, and unfolding a `def` are secondary semantics,
not substitutes for that derivation.

None passes. The first four declarations are `Iff.rfl` unfoldings (·103 is
literally a proposition iff itself). Item ·11 proves semantic function equality
using `funext` and `propext`. These are axiom-free Lean proofs, but no target is
a PM syntax tree and none inhabits a PM assertion judgement. In particular,
·1 does not replay its printed ✱21·3/✱35·01 route.

Graphs were rebuilt from zero. The only explicit printed graph in this lot is
·1 → {✱21·3, ✱35·01}; the other four source blocks print no citations. Since
all candidates fail before the judgement gate, their accepted Lean and
normalized graphs are empty. Constructor and definitional names are not
invented as historical dependencies.

All five records are `prepared` and blocked. CI evidence is pending; no
previously green Prop compilation is reused as v1 evidence.
