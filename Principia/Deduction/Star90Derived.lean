import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star90Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱90

The ancestral `R∗` of ✱90·01 is an incomplete relation abstraction.  The present
object syntax can express that abstraction only contextually through `star_21_01`;
it cannot return a relation-valued `Term`.  Consequently `R∗` cannot yet be
supplied to `applyBinary`, converse, relative product, image, restriction, or
the other eliminable operations occurring in every asserted formula of this
number.

The missing result is a pure derived conversion theorem, obtained from the
eighteen primitive constructors, which eliminates `star_21_01` inside an
arbitrary continuation.  No such theorem is currently available.  Declaring
an opaque relation atom or importing a host-language ancestral relation would
change PM's printed proposition, so no `⊢ᵣ` theorem is declared here.
-/

end PM.RamifiedSyntax
