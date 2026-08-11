# Q233 kernel-link continuation — exact opaque dependencies

The prior proof used local `Proof.mp`, `adj`, `syll`, and returned Star2/Star3
modules.  It is not a kernel link.  Use only these reviewed opaque/kernel
declarations: ✱2·08, ✱2·2, ✱2·53, ✱2·65, ✱3·26, ✱3·31, ✱3·43, ✱3·44,
✱3·47, ✱4·01.

Deliver only `star_4_43`, `star_4_44`, `star_4_45`, in order, preserving their
provided citation comments.  No `Proof.mp`, `adj`, `syll`, helper, local PM
module, import, redefinition, `Classical`, `axiom`, `sorry`, `admit`, or
`unsafe` is allowed.  If the listed interface cannot form a printed step,
return the per-target missing declaration instead of deriving a replacement.
