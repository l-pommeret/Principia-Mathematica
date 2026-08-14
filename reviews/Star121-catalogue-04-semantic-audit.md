# ✱121 catalogue 04 strict semantic audit

Four of the five loci pass strict typed equivalence. Propositions ✱121·14,
·141, ·142, and ·143 preserve the displayed converse operation, endpoint
swap, and the open, half-closed, or closed interval variant. Their extensional
Lean proofs establish exactly the printed equalities without extra premises.

Proposition ·13 is refused. PM compares `f(ν_P)` with
`f(P̌_{ν−_c1}ʻBʻP)`, whereas Lean states `f x ↔ f x`. Identifying the two
arguments silently erases the entire mathematical content inherited from
·04; reflexivity does not formalize the printed equivalence.

All five source readings match their literal blocks and print no numbered
dependencies. The four accepted proofs call no numbered Lean theorem. They are
promoted to `awaiting-ci`; ·13 is isolated without duplication in the refused
manifest as `blocked-non-equivalent-lean-statement`. CI evidence remains
pending.
