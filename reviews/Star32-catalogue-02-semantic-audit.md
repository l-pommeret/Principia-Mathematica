# ✱32 catalogue 02 corrected T2–T5 audit

The five literal source blocks PM1:✱32·11, ·111, ·12, ·121, and ·132 match their catalogue records and were compared individually with the declarations in `Principia/Architecture/Star32ConsecutiveKernel.lean`.

The earlier host-level semantic comparison is retained only as secondary
evidence. It does not justify `pm-derivation-v1`, and the five former
`kernel-checked` classifications are withdrawn to `prepared/blocked`.

- T2 passes for every item: the mapped declaration exists, is a theorem, and
  its module is in the `Principia.lean` import closure.
- T3 fails for every item: each theorem concludes an ordinary host `Prop`, not
  an inductive PM object-language derivation judgment.
- T4 fails for every item: no concrete elementary or ramified reading maps the
  exact printed string to a parsed relation/class AST endpoint.
- T5 passes for every item: targeted `#print axioms` reports no axioms for
  `star_32_11`, `star_32_111`, `star_32_12`, `star_32_121`, or `star_32_132`.

In particular, the `rfl` equalities ·11/·111 and direct existential witnesses
·12/·121 are valid secondary Lean facts but are not PM derivations. The
host-`Prop` biconditional ·132 is blocked for the same T3/T4 reason.

The previously recorded empty Lean graphs remain descriptive of the secondary
proof bodies only. No item is promoted by this audit.
