import Principia.Deduction.Star35Derived
import Principia.FirstEdition.Volume1.Star36Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱36

The 24 catalogue items were audited against `Star36Source`.  The definition
✱36·01 abbreviates `P⟏α` by the double restriction `α◁P▷α`; it cannot return a
relation-valued `Term`, because PM relation abstractions are contextual
`Formula.incompleteScope` nodes.  Consequently the first assertion, ✱36·11,
already needs the unavailable derivational conversion between a contextual
relation abstraction and its application/equality (the role of ✱21·3 in the
printed calculus).

The remaining assertions use ✱35 restriction laws and relational
extensionality.  `Star35Derived` records that neither layer is presently
available as a ramified `Derivation` theorem.  The host-logic theorems under
`Principia.Architecture` are deliberately not imported: they use Lean
functions, predicates, equality, and logical connectives in place of PM's
object syntax and therefore cannot establish `⊢ᵣ`.

No assertion is weakened to a reflexive expansion and no conclusion is
introduced as a premise.  Hence there is currently no pure theorem declaration
in this module.
-/

end PM.RamifiedSyntax
