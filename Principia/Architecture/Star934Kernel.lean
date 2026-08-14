import Principia.Syntax.Ramified

namespace PM.Architecture.Star934Kernel

open PM.RamifiedSyntax

/-!
# PM I ✱9·34: fixed universal injection

The printed chain is `✱1·3; ✱9·13; ✱9·21; (✱9·04)`.  The completed
✱9·21 evidence remains a closed canonical Raw judgement, rather than an
`OrderedAssertion`; this module records its one source-authorized application
to the displayed line (2), not a generic detachment from Raw evidence.
-/

/-- PM I ✱9·34 in the ramified object calculus. -/
theorem derive
    (universal : signature.Universal argument 0)
    (negation : signature.Negation 0)
    (disjunction : signature.Disjunction 0)
    (p : Formula signature real [] 0)
    (phi : Formula signature real [argument] 0) :
    ⊢ᵣ star_9_34_formula universal negation disjunction p phi :=
  PM.RamifiedSyntax.star_9_34 universal negation disjunction p phi

end PM.Architecture.Star934Kernel
