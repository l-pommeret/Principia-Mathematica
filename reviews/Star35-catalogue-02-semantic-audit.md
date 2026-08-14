# ✱35 catalogue 02 strict semantic audit

The five literal source blocks PM1:✱35·1, ·101, ·102, ·103, and ·11 match
their catalogue records and the declarations in
`Principia/Architecture/Star35ConsecutiveKernel.lean`.

All five translations pass strict equivalence. The Lean definitions interpret a
class as a predicate and a relation as a typed binary predicate. Accordingly,
·1, ·101, and ·102 are the exact pointwise laws for left, right, and
simultaneous restriction. In ·103, the displayed application of PM's Cartesian
relation `α ↑ β` is represented pointwise by `a x ∧ b y`; the apparently
tautological Lean statement therefore preserves, rather than drops, the whole
printed proposition. Finally, ·11 is extensional equality of the simultaneous
restriction with the pointwise intersection of both one-sided restrictions.

PM prints the dependencies ✱21·3 and ✱35·01 for ·1. Its Lean proof is
judgmental after unfolding `leftRestriction`, so neither citation remains as a
Lean theorem constant; the metadata records this exact, reviewed historical
closure relaxation. The other four demonstrations print no numbered dependency,
and their Lean bodies call no theorem declarations. No non-logical assumption is
introduced.

All five records are promoted in place to `awaiting-ci`; CI evidence remains
pending. No item is refused.
