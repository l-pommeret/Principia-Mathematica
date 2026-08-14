import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star72Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱72

The source catalogue contains 114 asserted propositions.  Their theory of
serial, connected, and related relation classes is built on the relation-class
constructions and derived theorems of ✱70 and ✱71.  Those predecessor
modules currently provide no exact `⊢ᵣ` theorem: the first obstruction is
the unavailable derived elimination/definition-conversion rule for the
contextual relation abstraction `star_21_01` used by ✱70·01 and ✱70·1.

Thus the cited premises of the printed ✱72 demonstrations cannot presently
be supplied as `Derivation` values.  The similarly named host-language
predicates in `Star72Source` are diplomatic catalogue aids, not PM object
formulae, and importing their proofs would violate both the object-judgement
and purity requirements.  No theorem is declared rather than certifying a
weakened or opaque surrogate.
-/

end PM.RamifiedSyntax
