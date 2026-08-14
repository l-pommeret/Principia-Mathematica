# Q279 PM-derivation migration audit — ✱11·26, ·27, ·3, ·31

This audit excludes ✱11·25, whose syntax-level migration is owned separately.
The four remaining declarations formerly marked canonical are constructive
Lean `Prop` theorems, but none is a PM object-language judgement or a closed
certificate replaying the printed demonstration. They are retained only as
secondary modern readings under `_prop` names.

The historical graphs were rebuilt directly from the printed lines:

- ✱11·26 cites ✱10·1·28 and ✱10·11·21;
- ✱11·27 cites ✱4·2, ✱11·03, ✱10·11·281, and ✱11·04;
- ✱11·3 cites ✱10·21 and ✱10·21·271;
- ✱11·31 cites ✱10·22 and ✱10·22·271.

The renamed `Prop` proofs call no PM theorem or derivation constant, so their
direct Lean and normalized PM graphs are both empty. No dependencies are
inherited from the old metadata.

The precise missing layer is closed composition at higher apparent arity.
Existing ✱10 contracts certify unary targets or expose action schemas, but no
current constructor takes the cited contracts and returns the exact binary or
ternary asserted `Raw` endpoints for these four demonstrations. A reflexive
`targetReading`, a tuple of unrelated prerequisites, or direct Lean quantifier
reasoning would not fill that gap. All four items therefore revert to
`prepared`, `blocked-no-pm-derivation`, and `prop-reading-only`; none receives
`pm-derivation-v1`.
