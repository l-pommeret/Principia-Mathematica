# ✱101 catalogue 03 strict semantic audit

Scope: exactly PM2:✱101·24, ·241, and ·25 from Q406, collated against
the literal source blocks for first-edition p. 21 / scan leaf 61 and compared
with the namesake declarations in `Star101Kernel.lean`.

Two candidates are refused.  ✱101·24 says that existence of an arbitrary
class `α` entails existence of the cardinal intersection `1 ∩ Clʻα`; Lean's
`star_101_24` merely proves that a displayed singleton has cardinal one.  It
omits the antecedent, intersection, `Cl`, and contextual existence claim.
✱101·241 asserts existence of the cardinal object `1`; Lean's
`star_101_241` assumes an inhabited carrier and then constructs an underlying
singleton class.  It both adds a hypothesis and changes the object whose
existence is asserted.

✱101·25 passes strict typed equivalence.  In the explicit characteristic-
predicate reading already used for finite cardinal membership, `Card1 a`
means `a ∈ 1`, `Included b a` is class inclusion, `a ≠ b` is the separately
printed inequality, and `Card0 b` means `b ∈ 0`.  Thus
`Proper b a := Included b a ∧ b ≠ a` retains every source hypothesis and the
conclusion.  The proof introduces no extra assumption and handles arbitrary
typed classes `a` and `b`.

Lean proves ·25 directly from the characteristic predicates, so none of its
printed citations is a direct theorem-constant dependency.  They remain in
the historical graph under a reviewed `relaxed-closure`; no dependency beyond
print is added.  Exactly ·25 is promoted to `awaiting-ci` in the canonical
Q406 catalogue.  The two refusals remain `prepared` in the homogeneous
Q406-refused catalogue; each PM ID occurs in exactly one of those files.
