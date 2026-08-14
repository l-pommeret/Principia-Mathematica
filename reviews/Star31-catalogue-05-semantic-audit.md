# ✱31 catalogue 05 strict semantic audit

Scope: exactly ✱31·51 and ·52, checked against their literal PG78050 blocks
and `Star31ConverseKernel3.lean`.

Both declarations pass strict homogeneous typed equivalence.  With
`f : Relation α → Prop`, ·51 quantifies over every relation and states that
precomposition by converse leaves universal quantification invariant.  ·52
states the corresponding existential equivalence.  Converse is an involution,
so both directions in each biconditional are retained without any extra
hypothesis or restriction on `f`.

The Lean proofs use only definitional converse involution and no numbered
theorem constant.  For ·52, the printed ·51 and `Transp` steps remain
historical unused dependencies under a reviewed relaxed closure; nothing
beyond print is added.  Both records are promoted to `awaiting-ci`, with CI
evidence pending.

