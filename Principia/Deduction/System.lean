import Principia.Syntax.Formula

namespace PM

/-- Boundary of the reconstructed PM calculus. Constructors are intentionally
absent until the corresponding primitive propositions and inference rules have
source-critical records. This prevents accidental import of Lean's deduction
rules as rules of PM. -/
inductive Derivation : Formula → Prop

notation:45 "⊢ₚ " p => Derivation p

end PM
