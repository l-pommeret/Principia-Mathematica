# Q224 continuation — authorized implicit-detachment relaxation

The strict retry is preserved as failure evidence.  This continuation has one
and only one editorial relaxation, at each of the three theorem loci
`PM1:✱3·33`, `PM1:✱3·34`, and `PM1:✱3·35`:

- authorize the primitive inference `PM.Derivation.star_1_1` **exactly for the
  `Γ = []` branch of detachment**;
- the already printed/whitelisted `PM.Derivation.star_1_11` remains the
  detachment branch for `Γ ≠ []`.

Classification: `incomplete-printed-inference/implicit-detachment-gap`.
`strict=false` applies only to that exact empty-context detachment event for
these three loci.  No other permission is added.

Reconstruct the three original declarations in their original order and with
their exact generic statements.  Use the exact printed theorem citations:

1. ✱3·33: ✱2·06 and ✱3·31;
2. ✱3·34: ✱2·05 and ✱3·31;
3. ✱3·35: ✱2·27 and ✱3·31.

For every target, make the detachment event explicit and auditable: show the
minor and major premises, invoke ✱1·1 only in the empty-context branch and
✱1·11 only with its `Γ ≠ []` witness in the nonempty branch.  Deliver a
per-target ledger listing the printed citations, both possible detachment
branches, which branch is the single authorized relaxation, and confirmation
that no other extra declaration occurs.

Do not use `PM.Derivation.star_1_2` through `star_1_6`, any unlisted Star1,
Star2, or Star3 proposition, any other primitive rule, local helper carrying
unlisted proof content, `Classical`, axioms, `sorry`, `admit`, `unsafe`, or
semantic shortcuts.  Preserve the exact target ASTs and return a complete
self-contained compiling Lean file.
