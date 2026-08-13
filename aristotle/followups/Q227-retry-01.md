# Q227 strict reconstruction continuation — reject primitive extras

The preceding terminal task compiled, but its result is **rejected** for this
strict batch.  It constructed proof plumbing by calling
`PM.Derivation.star_1_2`, `star_1_3`, `star_1_4`, `star_1_5`, and
`star_1_6` (and thereby used PM ✱1·2–✱1·6) inside the proofs.  Those are not
licensed by the exact per-target whitelists.  The fact that they occur in the
isolated context, or are primitive constructors, grants **no** proof
permission.

Reconstruct the entire requested Q227 batch again, retaining the two purely
definitional declarations and the three theorem declarations exactly as in the
original request, in exactly the same order:

1. `PM.Elementary.equiv` (definition only; no proof permissions),
2. `PM.Elementary.equivChain` (definition only; no proof permissions),
3. `PM.FirstEdition.Volume1.Star4.star_4_1`, using exclusively
   `PM.FirstEdition.Volume1.Star2.star_2_16` and `star_2_17`,
4. `PM.FirstEdition.Volume1.Star4.star_4_12`, using exclusively
   `PM.FirstEdition.Volume1.Star2.star_2_03` and `star_2_15`,
5. `PM.FirstEdition.Volume1.Star4.star_4_13`, using exclusively
   `PM.FirstEdition.Volume1.Star2.star_2_12` and `star_2_14`.

For each theorem, use no earlier local target unless its own whitelist allows
it (none do).  You may use Lean syntax, definitional unfolding/reduction, and
the exact allowed Lean declarations above only.  Do **not** call or refer to
any `PM.Derivation.star_1_*` constructor, any `PM.FirstEdition.Volume1.Star1.*`
theorem, `PM.Derivation.detach`, any unlisted Star2 theorem, or any helper
lemma whose proof uses one of those forbidden items.  Do not introduce axioms,
`sorry`, `admit`, `unsafe`, `Classical`, or any unlisted local axiom/helper.

The isolated context remains compilation scaffolding only.  It does not widen
the whitelist.  If one of the requested theorem targets is not derivable under
these constraints, provide a short Lean impossibility witness/diagnosis which
identifies the exact missing printed citation; do not silently relax the
policy.  Return the complete self-contained Lean file and an explicit per-
target citation ledger.
