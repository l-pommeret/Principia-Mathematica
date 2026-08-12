# Q287 exact Lean audit

PM I pp. 165--166 (scan leaves 187--188) records ✱11·6, ✱11·61--63,
and ✱11·7.  The formalization retains every displayed quantifier and both
argument positions.

For ✱11·6, PM's nested colon scopes read as
`∃x, ((∃y, φ(x,y) ∧ ψ(y)) ∧ χ(x))` on the left and the corresponding
`x`/`y` regrouping on the right.  The Lean proof merely transports the two
existing witnesses.  In ✱11·61 the existential `y` scopes over the antecedent
formal implication, so its witness is available uniformly before `x` is
introduced.  ✱11·62 is the printed exportation equivalence, ✱11·63 derives
the formal implication from the negated binary existential, and ✱11·7 uses
the type-correct swap forced by the occurrences `φ(x,y)` and `φ(y,x)`.

All five propositions are proved constructively and polymorphically.  There
is no `Classical`, decidability, inhabitedness hypothesis, new axiom, `sorry`,
semantic stub, or invented generic quantifier rule.  The historical PM
citations remain in metadata, while the Lean kernel checks the complete
resulting propositions directly.
