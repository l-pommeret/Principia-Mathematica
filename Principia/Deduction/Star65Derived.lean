import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star65Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱65

No proposition of ✱65 is declared here yet.  Its seven definitions use the
relative types of ✱64 to restrict classes and relations (`αₓ`, `Rₓ`, and the
two-sided restrictions).  Those relative-type operators are not yet reducible
constructions of `PM.RamifiedSyntax`, so the exact matrices of ✱65·13–·3
cannot be formed.

`Architecture.Star65Kernel` instead represents classes and relations by Lean
functions into `Prop`; its extensional results use host logic and are not
values of the eighteen-constructor `Derivation` judgement.  Importing them,
or replacing the restrictions by opaque atoms, would violate both the object
syntax and purity contracts.
-/

end PM.RamifiedSyntax
