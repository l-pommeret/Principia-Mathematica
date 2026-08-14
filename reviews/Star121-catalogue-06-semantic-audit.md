# ✱121 catalogue 06 strict semantic audit

Propositions ✱121·24 and ·241 pass strict typed equivalence. They preserve the
strict-order premise and identify each half-closed interval with the open
interval union the appropriate singleton endpoint.

The other three are refused. Lean ·231 omits field membership, reverse
implications, and existence. Lean ·242 assumes and returns reflexive equality
of one interval, omitting both singleton-union equalities. Lean ·251 is
reflexivity of `LeftClosed P Q` and never applies PM's strict-part operation.
The two exact records are `awaiting-ci`; the refusals remain `prepared` with a
blocking integration status.
