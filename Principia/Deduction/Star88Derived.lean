import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star88Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱88

The forty-six asserted propositions requested from ✱88 require cardinal
products, multiplicative classes, selections, domains, images, and the
preceding unformalized class calculus.  These notions have no reducible
object-syntax definitions or derived conversion rules in `RamifiedSyntax`.
The host-language `MultiplicativeAxiom` in `Star88OpeningKernel` is not a PM
object claim and cannot be imported as evidence.  In particular, any future
theorem depending on the printed multiplicative axiom must expose the
non-logical hypothesis `PM2:MULTIPLICATIVE`; no such dependency is hidden here.

No theorem is declared until the required object-calculus layer exists.
-/

end PM.RamifiedSyntax
