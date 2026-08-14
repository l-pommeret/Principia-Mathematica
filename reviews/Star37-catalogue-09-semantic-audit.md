# ✱37 catalogue-09 semantic audit

All five declarations in this batch pass strict item-level semantic audit and
are promoted to `awaiting-ci`.

- ✱37·212 preserves the dotted intersection of relations and the intersection
  of input classes, then supplies all four displayed image memberships.  Its
  left-associated Lean conjunction is only a parenthesization of PM's chain.
- ✱37·221 interprets the dotted union pointwise and proves equality of its image
  with the union of the two component images in both directions.
- ✱37·222 performs the complete four-case distribution over relation union and
  class union.  Every displayed summand is present exactly once.
- ✱37·23 defines `imageRelation R A B` as `A = image R B`; its domain therefore
  is exactly the class of classes that are images under `R`, matching PM's
  abstraction without an additional premise.
- ✱37·231 proves that every input class belongs to the converse-domain of the
  image relation, witnessed by its own image.  `universalClass (Class β)` is the
  typed counterpart of PM's `Cls` here.

The direct Lean terms for ·212 and ·222 reconstruct their witness cases rather
than invoking the predecessors printed in PM.  At ·23, the two printed citations
have become definitional through `imageRelation` and `domain`.  These are
recorded as reviewed `printed_but_unused` dependency relaxations; they do not
weaken any theorem statement.
