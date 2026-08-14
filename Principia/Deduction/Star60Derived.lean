import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star60Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱60

The twelve propositions of ✱60 carrying a printed `Dem.` have been audited
first: ✱60·321, ·33, ·371, ·38, ·53, ·55, ·7, ·32, ·37, ·45, ·5, and ·501.

They cannot yet be replayed as `Derivation` values.  Their printed first lines
use earlier class propositions (in particular ✱60·2, ✱51·15, ✱60·21,
✱40·1, and ✱40·11).  None of those propositions is currently exposed as a
ramified `⊢ᵣ` theorem.  More fundamentally, `star_20_01` constructs the
contextual class-abstraction node, but the calculus has no derived
definition-conversion theorem relating membership in that abstraction to its
matrix.  Thus the formulae required by the first printed lines cannot yet be
obtained from the eighteen primitive constructors.

No theorem is declared here: treating the extensional Lean kernels as
premises, or representing each displayed equality by an opaque propositional
atom, would not state the printed PM proposition in the object calculus.
-/

end PM.RamifiedSyntax
