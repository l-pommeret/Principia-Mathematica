# Q283 canonical integration — PM I ✱11·42–45

The five printed formulas are represented by independent `Raw` targets in
`Star11Q283Kernel.lean`.  Every occurrence of `(x,y)` and `(∃x,y)` is encoded
as two explicit ordered binders; constants are weakened through both bound
places rather than silently substituted.

Each declaration carries a kernel-checked truth-functional certificate for
the exact two-variable quantifier pattern and records the printed ✱10 route.
In particular, ✱11·43 retains the PM inhabited type discipline explicitly as
`Nonempty α` and `Nonempty β`; it is not asserted for empty modern carriers.
No `sorry`, new axiom, generic Raw detachment, or narrowed example is used.

Targeted verification:

```text
lake env lean Principia/Architecture/Star11Q283Kernel.lean
```

passes with Lean 4.30.0.
