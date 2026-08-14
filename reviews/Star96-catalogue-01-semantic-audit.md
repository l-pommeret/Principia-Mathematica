# ✱96 catalogue 01 semantic audit

The five loci ✱96·01, ·02, ·1, ·101, and ·102 were checked against
Project Gutenberg 78050 and the first-edition scan at printed page 640 (scan
leaf 662). Their formulas and displayed dependency brackets agree with the
canonical witness.

The typed reconstruction interprets `R_po` as the nonempty transitive closure
of `R`, `R_*` as its field-restricted reflexive closure, and the converse image
`R_*⃖ʻx` as `fun z => ReflexiveClosure R x z`. Under those interpretations,
`Ipart` is literally the intersection printed at ·01, while `Jpart` is literally
posterity minus `Ipart` as printed at ·02. The membership equivalences ·1 and
·101 then preserve both conjuncts and the negation exactly.

For ·102 the pre-existing helper declarations separately proved union and
disjointness. The canonical declaration `star_96_102` now packages the two
displayed claims as one conjunction, with the equality orientation printed by
PM and the empty class represented extensionally by `fun _ => False`.

All five declarations are closed theorem/definition bodies without `sorry`,
`admit`, axioms, or unsafe escape hatches. They are therefore marked
`awaiting-ci`; no CI success is claimed by this local audit.

The Lean proofs are extensional reconstructions, not replays of PM's printed
derivations. Thus the historical citations on ·1, ·101, and ·102 are retained
in the PM graph and declared as unused by the theorem-specific Lean closure.
The two unnumbered `star_96_102_*` helpers are local implementation details,
not additional canonical PM dependency nodes.
