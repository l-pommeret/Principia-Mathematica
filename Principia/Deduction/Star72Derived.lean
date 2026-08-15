import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star72Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱72

The source catalogue contains 114 asserted propositions.  Their printed
demonstrations use ✱71 throughout; for example the first proof, ✱72·1,
uses ✱71·17 and ✱71·103.  No unconditional `Derivation` values for those
premises exist while ✱70·1 remains conditional on
`reducibility_scope_transport`.

At the object-tree level, the obstruction is inherited unchanged: the
relation-class definition required by ✱70·01 has a `.sometimes` binder of
sort `.function [relationSort relationOrder 0] conditionOrder 0`, but the
available ✱20·3 result is specialized to a `.sometimes` binder of sort
`classSort resultOrder 0`.  The two binders do not reduce to the same
constructor index.

The similarly named host-language predicates in `Star72Source` are diplomatic
catalogue aids, not PM object formulae.  No conditional ✱72 assertion is
declared from unavailable ✱71 premises.
-/

end PM.RamifiedSyntax
