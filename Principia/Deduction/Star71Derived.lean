import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star71Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱71

The source catalogue contains 138 asserted propositions.  The first printed
route, ✱71·01 by ✱70·4, already needs an unconditional ✱70 consequence;
✱70·4 in turn cites ✱70·1.  The latter is presently available only with
the explicit `reducibility_scope_transport` recorded in `Star70Derived`.

This is not an absence of class or relation syntax.  The exact obstruction is
the one recorded there: the `.sometimes` root of `star_20_3_formula` binds
`classSort resultOrder 0`, built from the argument sort `.individual`, while
the ✱70·01 instance must bind
`.function [relationSort relationOrder 0] conditionOrder 0`.  Those
`SortCode.function` indices are distinct.  Although ✱10·35 itself is now
proved, the available ✱20·3 theorem remains conditional on the stronger
contextual reducibility-scope transport.

The host predicates in `Star71Source` are therefore not used as substitutes
for PM formulae.  No conditional ✱71 assertion is propagated from the
conditional ✱70 result.
-/

end PM.RamifiedSyntax
