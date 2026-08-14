import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star51Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱51

No proposition of ✱51 is declared here yet.  The opening proof ✱51·1 already
requires the application and elimination of the contextual relation
abstraction used by ✱51·01 (through ✱32·1 and ✱50·1).  `star_21_01` correctly
represents such an abstraction by `Formula.incompleteScope`; it is not a
relation-valued `Term`, and the current eighteen constructors of `Derivation`
provide no derived elimination theorem for that scope.

The later printed proofs depend on that opening sequence or on the analogous
contextual singleton-class construction.  Assuming any of those target
assertions would hide more than a missing ✱13 theorem, so the measured honest
total for this module is zero `⊢ᵣ` theorem declarations.
-/

end PM.RamifiedSyntax
