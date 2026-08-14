import Principia.Deduction.Star23Derived
import Principia.FirstEdition.Volume1.Star24Source

namespace PM.RamifiedSyntax

/-!
# PM I, ✱24 — asserted propositions

The catalogue contains 72 items: three eliminable definitions and 69
assertions.  None of the 69 assertions can yet be stated faithfully as a
theorem of `Derivation`.

The first assertion, ✱24·1, cites ✱22·351 after unfolding ✱24·02.  The
ramified calculus currently has neither the ✱22 class complement operation
nor a derived rule eliminating the contextual class abstraction produced by
`star_20_01`.  In particular, the universal and null classes are not
standalone `Term`s that could be passed to `star_13_01`.  Every later
assertion uses the same missing contextual elimination, directly or through
class membership, inclusion, intersection, union, complement, or difference.

Introducing a class-valued constant, replacing PM identity by Lean equality,
or adding a constructor to `Derivation` would violate the purity contract.
Consequently this module deliberately declares no theorem.  The exact missing
prerequisite is a pure derived elimination theorem for `star_20_01`, followed
by ramified definitions and pure derivations of the five operations of ✱22.
-/

end PM.RamifiedSyntax
