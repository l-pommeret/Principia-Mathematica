# Q293 exact Lean audit

The diplomatic source on PM I p. 178 (scan leaf 200) contains ✱13·181,
✱13·182, ✱13·183, ✱13·19, and ✱13·191.  The Lean module uses
polymorphic intensional equality and preserves every displayed variable.

✱13·181 transports inequality along `x = y`; ✱13·182 transports the
right-hand argument of `z = _`; and the formal-equivalence subscript `z` in
✱13·183 is represented by `∀ z, (z = x ↔ z = y)`.  ✱13·19 retains its
existential witness.  In ✱13·191 the formal implication subscript `y` is the
universal binder `∀ y`, so instantiating it at `x` yields the reverse direction.

All five are complete kernel proofs.  They require no classical reasoning,
inhabitedness, decidability, new axiom, placeholder, or semantic stub.  The
printed historical dependencies remain separately recorded in metadata.
