import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star70Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱70

The source catalogue contains 44 asserted propositions.  Their first required
object-language step is ✱70·1, obtained by expanding the contextual relation
abstraction of ✱70·01 through ✱20·3.  In `RamifiedSyntax`, relation
abstraction is deliberately represented by `star_21_01`, whose result is an
`incompleteScope` formula rather than a standalone relation term.

The current eighteen-constructor `Derivation` judgement has no derived
elimination or definition-conversion theorem which rewrites application or
membership through that contextual abstraction.  `Star21Derived` consequently
exports no `⊢ᵣ` version of ✱21·1 or ✱20·3, so the printed proof of ✱70·1
cannot be started.  Every later assertion in ✱70 depends on ✱70·1, directly or
through another result of the section.

The extensional `Arrow` definition in `Star70Source` is a host-language `Prop`
using Lean quantifiers and conjunction.  It cannot replace the printed PM
formula in an object-calculus theorem.  No theorem is therefore declared here;
doing so would require either weakening the assertion or adding a primitive
rule, both forbidden by the certification contract.
-/

end PM.RamifiedSyntax
