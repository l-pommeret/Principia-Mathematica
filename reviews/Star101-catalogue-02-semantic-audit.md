# ✱101 catalogue 02 strict semantic audit

Scope: exactly PM2:✱101·14, ·15, and ·16 from
`PM2-star-101-Q405.json`.  Their literal source blocks in
`Star100Source.lean` agree with the canonical catalogue and first-edition
p. 20 / scan leaf 60.  The following comparison is signature-level: theorem
names and elementary consequences of `a = empty` do not establish equivalence
with PM's cardinal operations.

All three candidate declarations in `Star101Kernel.lean` are refused.

- **✱101·14.**  PM states `Ncʻγ = 0 ≡ γ = Λ`, relating the cardinal-number
  operation to the null class.  Lean's `Card0 a ↔ a = empty` is `Iff.rfl`
  because `Card0` was defined as that right-hand equality.  It contains no
  `Nc`, no cardinal object `0`, and no interpretation map connecting the
  newly defined predicate to those source objects.  The substantive left side
  has therefore been replaced by the desired conclusion.
- **✱101·15.**  PM states the image identity `smʻʻ0 = 0`.  Lean's
  `star_101_15` takes two underlying sets already assumed `Card0` and concludes
  that they are equal.  There is no `sm` relation/image, no cardinal class as
  input or output, and the quantifier structure differs from the source.
- **✱101·16.**  PM quantifies over a nonzero cardinal `μ ∈ NC − ιʻ0` and says
  contextually that every `α ∈ μ` exists.  Lean instead proves that a predicate
  `a : α → Prop` not equal to `empty` has a member.  It omits `NC`, the
  singleton exclusion of the cardinal object `0`, the outer cardinal
  membership, and the printed subscripted universal implication.

No item is promoted to `awaiting-ci`.  The three canonical records remain
`prepared` and now carry their refusal evidence directly, preserving exactly
one metadata record per PM ID.  Their Lean dependency lists are empty because
none of the candidate declarations is accepted as a formalization.
