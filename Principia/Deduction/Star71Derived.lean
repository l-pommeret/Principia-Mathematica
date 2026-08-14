import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star71Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱71

The source catalogue contains 138 asserted propositions.  Its opening
assertions ✱71·01--·04 are specializations of ✱70·4, ✱70·41, and ✱70·42;
the subsequent proofs repeatedly cite those results and ✱70·1x--·5x.
The current derived layer cannot expose any of these as `⊢ᵣ` derivations because the
calculus lacks the derived elimination/definition-conversion theorem for the
contextual relation abstraction `star_21_01`.

Consequently even the first printed bracket proof, ✱71·01 by ✱70·4, has no
object-judgement premise to specialize.  Replacing one-many, many-one, or
one-one relations by the host predicates in `Star71Source` would introduce
Lean's `Prop`, quantifiers, equality, and connectives in place of PM's own
syntax.  No exact theorem is declared until the missing ✱20/✱21 conversion
layer and its ✱70 consequences are derived from the eighteen primitives.
-/

end PM.RamifiedSyntax
