import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star41Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱41

The source contains 45 asserted catalogue propositions about products and
sums of classes of relations.  None is presently expressible as the exact
claim of a pure `⊢ᵣ` theorem.

Already ✱41·1 and ✱41·11 require applying the contextual relation
abstractions defined by ✱41·01 and ✱41·02.  The available constructor
`star_21_01` represents such an abstraction by `Formula.incompleteScope`, not
by a relation-valued `Term`.  `Derivation` has no derived rule that unfolds
that scope into relation application.  Thus the defining membership
equivalences cannot be formed by weakening or reflexivity, and all later
claims about containment, converse, restriction, domain, field, and relative
product inherit the same obstruction.

Opaque atoms or the extensional host-logic kernels under
`Principia.Architecture` cannot be used as premises of `Derivation`; doing so
would cease to derive the printed PM formula from its eighteen primitives.
Accordingly this module declares zero `⊢ᵣ` theorems.  What is missing is a
pure derived elimination/conversion theorem for contextual relation
abstraction (`star_21_01`), itself obtained without a nineteenth primitive.
-/

end PM.RamifiedSyntax
