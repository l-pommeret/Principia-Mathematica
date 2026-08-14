# ✱23 opening — strict v1 refusal

Scope: definitions ✱23·01–·05 and propositions ✱23·1, ·2, ·3, ·31, ·32,
first-edition printed page 226.

The attempted relation kernel was rejected. It represented the five printed
`Df` clauses as constructors of a proposition-valued derivation relation.
That makes eliminable definitions into new primitive assertions. It also made
theorems ·1–·31 restate those constructors instead of reconstructing their
printed demonstrations. The prototype is preserved only in
`archive/invalid-kernel-prototypes/Star23OpeningDerivation.lean`.

The active records are therefore source-only and `prepared`. A valid kernel
must encode ·01–·05 as unfolding definitions, formalize the earlier ✱22 rules
actually cited by the demonstrations, and derive the propositions using those
rules. In particular ·32 must compose ·05, ·02, and ·04 through genuine
equality transport; ·05 alone is not its proof.

No active Lean or normalized proof edge is claimed. The empty primary graph
records absence of a derivation, not proof completeness.
