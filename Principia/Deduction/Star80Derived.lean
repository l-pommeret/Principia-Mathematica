import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱80

The catalogue has 76 items: one definition and 75 assertions.  The selection
operator `P_Δʻκ` is a class of relations defined by a contextual class
abstraction.  Its very first assertion requires conversion between membership
in that abstraction and the displayed conjunction involving `1→Cls`, `RlʻP`,
and `ᗡʻR=κ`.  `Derivation` currently provides no theorem eliminating
`star_20_01` (nor the nested relation abstractions) in an assertion.  Hence the
opening assertion cannot be replayed, and every later printed demonstration
depends on it or on the same missing conversions.

The `Principia.Architecture.Star80*` declarations are host-logic surrogates;
the existing semantic audit also records reflexive/pass-through weakenings
there.  They are not imported.  No assertion is replaced by an opaque atom or
by a Lean predicate, and consequently no false certification is emitted.
-/

end PM.RamifiedSyntax
