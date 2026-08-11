# Q228 kernel-link continuation — strict printed permissions

The precompiled archive is not promotable: it introduced `Q228/Derived.lean`,
local Rules, `adjoin`, and a private rotation route that bypassed printed
dependencies.  Deliver only the four target theorem bodies, against the
reviewed repository-kernel context; no local PM module, helper theorem/rule,
definition of equivalence, wrapper, or namespace is permitted.

Use exactly these existing kernel declarations, per target:

- `star_4_11`: `Star2.star_2_16`, `Star2.star_2_17`,
  `Star3.star_3_22`, `Star3.star_3_47`.
- `star_4_14`: `Star3.star_3_37`, existing `Star4.star_4_13`.
- `star_4_15`: `Star3.star_3_22`, existing `Star4.star_4_13`, and the
  preceding local target `star_4_14` only.
- `star_4_2`: `Star2.star_2_08`, `Star3.star_3_2`.

No `adjoin`, `syll`, `imp_pre`, `imp_post`, `conj_mono_right`, private
rotation, detachment helper, primitive axiom, `Classical`, `axiom`, `sorry`,
`admit`, `unsafe`, import, or additional declaration is allowed.  The listed
constants are the complete strict whitelist.  In particular, do not use the
previous archive's alternative route for `star_4_15`.

If a listed body cannot be written under that exact whitelist, return a
per-target obstruction trace (required formula and missing PM locus); do not
guess a relaxation.  A source audit, not this continuation, decides whether a
minimal relaxation exists.
