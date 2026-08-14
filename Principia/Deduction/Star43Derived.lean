import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star43Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱43

The source contains 38 asserted catalogue propositions about relations with
limited domains and converse domains.  None can presently be represented and
proved exactly in `Derivation`.

The very first assertion, ✱43·1, applies the incomplete relation `(R |)` and
identifies that application with a limited relation.  Both the incomplete
relation abstraction of ✱21 and the class-valued restriction operations are
contextual constructions in `RamifiedSyntax`, not relation-valued `Term`s.
There is no derived rule among the current API which eliminates an
`incompleteScope` or substitutes its matrix into its continuation.  The
following assertions depend on that conversion directly or through the
domain, converse-domain, field, image, and restriction laws printed later in
the section.

Using host functions from the extensional architecture, replacing each
relation formula by an atom, or asserting a reflexive equality would not be a
derivation of PM's printed claim.  Therefore this module declares zero of 38
`⊢ᵣ` theorems.  The exact prerequisite is pure derived conversion for
contextual class and relation abstraction, followed by object-calculus
definitions of the limited-domain operations; no new primitive constructor
is admissible.
-/

end PM.RamifiedSyntax
