import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star52Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱52

No proposition of ✱52 is declared here yet.  Its definition ✱52·01 forms the
class of unit classes, and the first printed theorem ✱52·1 invokes ✱20·3 to
eliminate that class abstraction.  In the ramified syntax, class abstraction
is deliberately contextual (`star_20_01`, hence `Formula.incompleteScope`),
while the current `Derivation` API exposes no derived theorem eliminating this
scope.  The remaining propositions depend on ✱52·1 or on still richer class,
description, and relation constructions.

This obstruction is not a missing ✱13 theorem alone.  Introducing a
class-valued term or assuming a target assertion would violate the stated
contract, so the measured honest total for this module is zero `⊢ᵣ` theorem
declarations.
-/

end PM.RamifiedSyntax
