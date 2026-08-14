# ✱51 catalogues 05–06 — strict source/Lean semantic audit

The ten literal source statements PM1:✱51·232 through ·25 on printed pages
359–360 were compared with their complete declaration types and proof bodies
in `Star51OpeningKernel3.lean`. The direct typed interpretation maps PM's unit
class to `singleton`, class union to `Union`, class inclusion to `Included`,
and the displayed bound universal and existential formulas to Lean's ordinary
quantifiers with membership hypotheses.

All five items in catalogue 05 are exact. Declarations ·232 and ·233 preserve
the pointwise membership equivalence for two unit classes; ·234 and ·235
preserve respectively the universal conjunction and existential disjunction;
·236 gives the exact membership disjunction after adjoining one element.

All five items in catalogue 06 are also exact. Declaration ·237 is the
pointwise form under the printed class equality; ·238 and ·239 preserve the
full universal and existential scopes; ·24 turns unit-class inclusion into the
same membership disjunction; and ·25 retains both antecedents and the stated
inclusion conclusion.

The promoted set is exactly 10/10. Each record is promoted in place to
`awaiting-ci`; no refused sidecar is created and every proposition ID remains
unique. None of the ten source blocks has a bracketed numbered citation, and
the Lean proofs invoke no numbered proposition, so their printed, normalized,
and Lean proposition-dependency graphs are empty.
