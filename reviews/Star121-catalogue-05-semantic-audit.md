# ✱121 catalogue 05 strict semantic audit

Propositions ✱121·2, ·201, and ·202 pass strict typed equivalence: they
exclude respectively the left endpoint, right endpoint, and both endpoints
from an open interval under the displayed irreflexivity conditions. The proof
of ·202 reuses the first two Lean lemmas; this implementation-only closure is
recorded although PM prints no numbered citation.

Propositions ·22 and ·23 are refused. Lean proves only endpoint-membership
consequences under added premises; it omits the reverse directions and PM's
third existence member. The three exact records are `awaiting-ci`; the two
refusals remain `prepared` with a blocking integration status.
