import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star64Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱64

No proposition of ✱64 is declared here yet.  Its twelve defining loci form
relative relation types such as `t₀₀ʻα = tʻ(t₀ʻα ↑ t₀ʻα)`.  The ramified
syntax can type relation terms, but it does not currently provide these
relative-type operators as reducible object-syntax constructions.  The
one-carrier definitions in `Architecture.Star64Kernel` collapse the distinct
operand levels and state host-language equalities, so they cannot be imported
as `Derivation` evidence.

The first asserted proposition already depends on the missing definition
conversion, and the remaining printed assertions depend on it or on the same
relative-type constructions.  An arbitrary propositional atom or the
architecture-only model would therefore weaken the printed statements.
-/

end PM.RamifiedSyntax
