import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star53Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱53

No proposition of ✱53 is declared here.  Every displayed assertion in this
chapter uses a class as the argument or value of a class operation: singleton
classes, class union/intersection/difference, direct images, or the class of
unit classes.  The ramified syntax intentionally has no class-abstraction
`Term`: `star_20_01` is a contextual `Formula.incompleteScope`.

The current eighteen-constructor `Derivation` judgement has no derived
conversion theorem eliminating that contextual scope as the membership
formula required by ✱20·3 (nor the ensuing derived class-operation theorems).
Consequently an exact AST for the printed subjects cannot yet be formed from
the available public operations.  Treating a Lean set or equality as the
printed class, accepting the conclusion as a premise, or adding a primitive
constructor would violate T3, T6, T10, and the purity contract.

Thus the honest total is zero `⊢ᵣ` theorem declarations.  This is the
precise representational prerequisite that must be supplied in the deduction
layer before the 53 catalogue items assigned to ✱53 can be derived.
-/

end PM.RamifiedSyntax
