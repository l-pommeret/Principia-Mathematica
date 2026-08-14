# ✱121 catalogue 02 strict semantic audit

This audit covers exactly PM2:✱121·03, ·031, ·04, ·1, and ·101. Each
catalogue reading matches its literal `PM-VERBATIM` block and occurs in no
other metadata item.

Four translations pass strict typed equivalence. `Finid level` in ·03 is the
class of levels at admissible finite indices; the `Nat` index type supplies
PM's inductive-cardinal, non-null index restriction. The further `n > 0`
condition in `Fin level` preserves exactly the exclusion of zero in ·031.
Propositions ·1 and ·101 are the pointwise membership laws for the open and
left-closed interval definitions and retain both endpoint conditions.

Definition ·04 is refused. PM defines the indexed expression `ν_P` by the
image of `BʻP` under the converse of the predecessor level. The Lean declaration
states only `P x = P x`; it contains neither ν, the cardinal predecessor, the
converse operation, `B`, nor relational image. It is therefore a tautology, not
an abstraction of the printed definition.

All five loci print no numbered dependencies, and the four accepted Lean
declarations are judgmental unfoldings with no theorem dependencies. The four
exact records are promoted to `awaiting-ci`; ·04 is isolated in the refused
manifest as `blocked-non-equivalent-lean-statement`. CI evidence remains
pending.
