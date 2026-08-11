# Q231 kernel-link continuation — no local sequent calculus

The prior archive constructed a new `Prf`/`Ent` calculus with its own axioms,
weakening, deduction and introduction/elimination rules.  It is rejected for
linking.  Use the reviewed opaque/kernel constants only: ✱1·6, ✱3·01,
✱3·22, ✱3·45, ✱3·47, ✱3·48, ✱4·01, ✱4·32.

Deliver only the target definition `PM.Elementary.productChain` and the target
theorems `star_4_36`, `star_4_37`, `star_4_38`, `star_4_39`, in printed order.
The definition is a target; no other definition, theorem, rule, namespace,
import, local dependency, or wrapper is permitted.  Preserve the citation
comments already supplied in the interface.

If any listed opaque declaration is insufficient, report the target and exact
missing declaration.  Do not recreate a calculus or add `Classical`, `axiom`,
`sorry`, `admit`, or `unsafe`.
