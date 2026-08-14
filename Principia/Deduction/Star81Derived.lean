import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star81Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱81

The eighteen asserted propositions of ✱81 cannot yet be stated exactly as
ramified object formulae.  Their opening assumptions and conclusions already
use selection (`PΔʻκ`), domain and converse images, restriction, class
inclusion, relation equality, and similarity.  `RamifiedSyntax` currently has
no reducible object-syntax definitions for those operations and no derived
definition-conversion rule for the contextual class and relation abstractions
of ✱20 and ✱21.

The extensional Lean definitions in the first-edition kernel files are
host-language predicates and functions.  Importing their theorems, or hiding
each displayed construction in an opaque propositional atom, would not yield
the printed `⊢ᵣ` claims.  No theorem is therefore declared here.
-/

end PM.RamifiedSyntax
