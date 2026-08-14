# ✱32 catalogue 08 strict semantic audit

This audit compares the three canonical source blocks ✱32·4, ·41, and ·42
individually with `Star32ConsecutiveKernel4.lean` and
`Star32ConsecutiveKernel5.lean`.

✱32·4 passes: `FunctionalAt R y` is exactly existence of a member of the
right section together with subsingleton uniqueness, and the Lean theorem
proves both directions. ✱32·42 also passes: equality of right sections
transports existence and uniqueness in both directions, retaining the printed
antecedent and biconditional. Their proof bodies use only local definitions;
the direct Lean and normalized graphs are empty. The historical graph now
records the printed citations ·4 makes to ✱30·21 and ✱32·18 and ·42 makes to
✱30·34 and ✱32·18. Both exact items are promoted to `awaiting-ci`.

✱32·41 is refused. PM assumes only `E!Sʻy` outside the biconditional. Lean's
`star_32_41` instead requires both `r : FiberValue R y` and
`s : FiberValue S y` as global arguments. Supplying the R-value in advance
strengthens the premise; in print its meaningfulness must arise contextually
on the relevant side. The refusal is isolated in the homogeneous manifest
`PM1-star-32-catalogue-8-refused.json`.
