# Q226 final constrained correction

Correct the immediately preceding result while preserving only these licensed
exceptions: `star_3_45` may call `PM1:✱3·3` solely for its documented
implicit-exportation gap; `star_3_47` may call `PM1:✱3·2` solely in the
`Γ = []` branch and `✱3·03` in the nonempty branch.  In particular the direct
source of `star_3_47` must contain neither `star_3_3` nor a helper that invokes
it; it may use the local `star_3_45` only through printed `Fact`.

Remove every direct `PM.Derivation.star_1_5` / `star_1_6` occurrence from all
delivered Lean files; `Classical` is tolerated only in unused Main harness.
No other PM extra, axiom, sorry, admit, unsafe, semantic replacement, or
helper rule.  Return all four theorems and a literal per-file forbidden-token
scan plus target-local direct-citation ledger.
