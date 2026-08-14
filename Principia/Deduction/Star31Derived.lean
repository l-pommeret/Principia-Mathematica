import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star31Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱31

The contextual relation abstraction `star_21_01` can represent the definitions
✱31·01 and ✱31·02, but `Derivation` has no rule which unfolds or eliminates an
`incompleteScope` relation abstraction.  The first asserted proposition,
✱31·1, already requires precisely that missing derivational step.  Later
propositions depend on it or on other unavailable derived equality, description,
and relation rules.  In particular, the printed route for ✱31·13 cites ✱14·21
and ✱31·12: making ✱14·21 an explicit hypothesis still leaves ✱31·12
underived, so it cannot honestly close the assertion.

Consequently this module contains no theorem declaration: the existing
secondary `Prop` kernels are not proofs in the ramified PM judgement, and
turning definitional computation into a new constructor would violate the
closed list of eighteen primitive propositions.
-/

end PM.RamifiedSyntax
