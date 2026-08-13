# Q227 continuation — minimally relaxed equivalence-packaging gap

The strict continuation is preserved as a rejected archive and established a
real structural obstruction.  This continuation has the sole editorial
authorization below.  Its classification is
`incomplete-printed-citation/equivalence-packaging-gap`; `strict=false` only
at the three theorem loci listed here.  The two definition targets remain
strict and receive no proof permission.

Reconstruct the Q227 declarations in their original order and exact
statements.  Retain the original exact whitelist in each theorem and add
**exactly** these per-locus permissions:

| Target | Original citations | Authorized additions |
|---|---|---|
| `PM.FirstEdition.Volume1.Star4.star_4_1` (✱4·1) | ✱2·16, ✱2·17 | ✱3·2, and inference `detach` (✱1·1/✱1·11) |
| `PM.FirstEdition.Volume1.Star4.star_4_12` (✱4·12) | ✱2·03, ✱2·15 | ✱3·2, ✱3·47, and inference `detach` (✱1·1/✱1·11) |
| `PM.FirstEdition.Volume1.Star4.star_4_13` (✱4·13) | ✱2·12, ✱2·14 | ✱3·2, and inference `detach` (✱1·1/✱1·11) |

No other permission is granted.  In particular do **not** use any
`PM.Derivation.star_1_2`, `star_1_3`, `star_1_4`, `star_1_5`, or `star_1_6`,
any `PM.FirstEdition.Volume1.Star1.*` theorem, any unlisted Star2 or Star3
theorem, any unlisted rule, `Classical`, axiom, `sorry`, `admit`, `unsafe`, or
helper whose proof depends on one of them.  `PM.Derivation.detach` is allowed
only as the explicit authorized inference above; it is not a blanket primitive
permission.

Implement the authorized ✱3·2 and ✱3·47 material only as necessary to make
the printed packaging steps explicit and auditable.  Supply a per-target event
ledger showing: original printed events, each use of ✱3·2/✱3·47, every
`detach`, and confirmation that no other extra declaration occurs.  Return a
self-contained compiling Lean file containing the two definitions and all
three requested theorem declarations (not commented-out substitutes).
