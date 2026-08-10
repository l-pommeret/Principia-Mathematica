# Audit Q254 — PM I, ✱9·07, ✱9·08, ✱9·1 and ✱9·11

Verdict: **NOT A — blocked on higher-order operations and first-order
assertion**. Source: first edition,
vol. I, pp. 135–137, leaves 157–159. ✱9·07/08 are nested-binder disjunction
definitions and explicitly extend beyond pairs of elementary functions.
✱9·1 and ✱9·11 are printed primitive propositions, not Lean existential
rules. The latter cannot be obtained using ✱4·77 because that proof depends
on the very analogue of ✱1·2 still to be established. No PM print error is
established. Wikisource's `unchaged/unchanged` and `is/if` are digital-only
defects in the surrounding prose.

The kernel-checked `Quantified` type supports one generic binding step, but
the repository does not expose the fixed-order-polymorphic renaming,
weakening, and disjunction structure required by PM's explicit extension of
✱9·07/08 to functions not both elementary. An elementary-only target would
be a material narrowing. Separately, `PM.Derivation` is indexed only by
`PM.Elementary`, so it cannot state ✱9·1/11 as asserted first-order primitive
propositions. These are API gaps, not Aristotle proof obligations. No exact
Lean target can responsibly be frozen until both interfaces are audited and
kernel-checked. Confidence in source collation and this obstruction: high.
