# Q224 strict reconstruction continuation — minimize and expose proof events

Reconstruct the three original Q224 targets again, in the same order and with
the exact declarations and statements from `Q224.md`:

1. `PM.FirstEdition.Volume1.Star3.star_3_33`,
2. `PM.FirstEdition.Volume1.Star3.star_3_34`,
3. `PM.FirstEdition.Volume1.Star3.star_3_35`.

This is a strict retry.  For each target, use only its exact printed
whitelist, its explicitly licensed PM inference convention ✱1·11/`detach`,
Lean syntax/definitional reduction, and no other PM proposition or inference.
There are no licensed earlier local targets.  Every used printed theorem and
every detachment event must be visibly named in the target proof and listed in
a per-target ledger.  Do not conceal an unlisted dependency in a helper.

In particular, do not call `PM.Derivation.star_1_2` through `star_1_6`, any
unlisted Star1/Star2/Star3 declaration, any unlisted primitive rule, or any
unlicensed theorem from the supplied context.  Do not add axioms, `sorry`,
`admit`, `unsafe`, `Classical`, semantic shortcuts, or assumptions.  Preserve
the exact object-language ASTs; do not merely prove a related reassociation.

The initial archive is under independent audit.  If the empty-context branch
of the generic `detach` wrapper necessarily invokes ✱1·1 rather than the
licensed ✱1·11 convention, report that exact event honestly and leave the
affected target unproved with a machine-checkable diagnosis rather than
silently treating ✱1·1 as licensed.  Likewise report any other impossible
event rather than widening permissions.  Return a self-contained compiling
Lean file plus the citation/event ledger.
