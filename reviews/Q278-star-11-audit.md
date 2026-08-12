# Q278 exact-target audit

All five printed propositions on PM I p. 160 are represented by closed
canonical `Raw` targets in `Star11Q278Targets.lean`.  The two explicit
renamings preserve the printed binder order: `swapTwo` sends `(x,y)` to
`(y,x)`, while `rotateThree` sends `(x,y,z)` to `(y,z,x)`.

The reduction underlying ✱11·22 is kernel checked by
`star_11_22_definition`; it exposes the two applications of the primitive
quantifier-negation equations.  It is not, by itself, a derivation of the
displayed equivalence.

No item is promoted.  ✱11·2 requires the unformalized second-order Pp ✱11·07
and the transport rules cited as ✱11·1/✱11·11/✱11·12.  ✱11·21, ✱11·23, and
✱11·24 depend transitively on that missing permutation interface.  Until a
genuine second-order judgement and these source rules are kernel checked,
the exact targets remain `prepared`; recording an `rfl` target reading as a
proof would be unsound campaign metadata.
