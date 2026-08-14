# ✱32 catalogue 01 non-v1 proof audit

Scope: ✱32·13, ·131, ·16, ·1, and ·101. This corrected audit applies the
T1–T9 `pm-derivation-v1` gate, in particular the computed T2–T4 checks rather
than treating axiom-free host-`Prop` proofs as sufficient.

Verdict: **blocked/prepared for all five items**. The previous promotion of
✱32·13, ·131, ·1, and ·101 was overclassified and is withdrawn.

- T2 passes: each mapped declaration exists and is a theorem imported by
  `Principia.lean`.
- T3 fails: every conclusion is an ordinary Lean `Prop`; none has the form of
  an inductive PM object-language derivation judgment whose constructors are
  audited primitive propositions or inference rules.
- T4 fails: no concrete elementary or ramified reading connects the exact
  printed string to a parsed relation/class AST endpoint. The local function
  encodings `rightSection` and `leftSection` are secondary interpretations,
  not such readings.

- ·13 and ·131 are closed `rfl` proofs of the two displayed sectional
  equalities. Their source citations are unused because `rightSection` and
  `leftSection` compute to the encoded class abstractions. This establishes a
  useful secondary theorem but cannot satisfy T3 or T4.
- ·1 and ·101 are likewise closed `Iff.rfl` proofs. Neither accepts a
  sectional equality, a support certificate, or any form of the conclusion as
  an input, but reflexivity in host `Prop` is not a PM derivation judgment.
- ·16 proves the complete three-term equivalence chain by composing the
  independently proved extensional equivalences ✱32·14 and ✱32·15. It does
  not weaken the chain or assume any of its links. Nevertheless, `#print
  axioms` reports `Quot.sound`, inherited from the propositional extensionality
  required to turn pointwise equivalence into equality of relation-valued
  functions. It therefore additionally fails T5.

The primary graphs were recomputed from the declaration bodies. Items ·13,
·131, ·1, and ·101 have empty Lean graphs and exact relaxed-closure records
for their unused printed citations. Item ·16 has precisely the Lean and
normalized edges ·14 and ·15, matching the printed graph. `#print axioms`
reports no axioms for the four secondary declarations; ·16 reports
`[Quot.sound]`. These graph and axiom facts do not override the T3/T4 failure.
