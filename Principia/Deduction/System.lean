import Principia.Syntax.Formula

namespace PM

/-- Assertion in the reconstructed elementary PM calculus.

`Derivation [] p` represents assertion of a definite proposition. For nonempty
`Γ`, `Derivation Γ p` represents assertion of an elementary propositional
function with real variables; members of `Γ` are not hypotheses. -/
inductive Derivation : {Γ : RealContext} → Elementary Γ → Prop where
  /-- ✱1·1. Inference between asserted definite elementary propositions. -/
  | star_1_1 {p q : Elementary []} :
      Derivation p → Derivation (p ⊃ₚ q) → Derivation q
  /-- ✱1·11. Axiom of identification of type for one or more real variables.

  This remains distinct from ✱1·1 because PM treats assertion of a
  propositional function as a separate primitive idea. -/
  | star_1_11 {Γ : RealContext} {φ ψ : Elementary Γ}
      (hasRealVariable : Γ ≠ []) :
      Derivation φ → Derivation (φ ⊃ₚ ψ) → Derivation ψ
  /-- ✱1·2. Principle of tautology (`Taut`). -/
  | star_1_2 {Γ : RealContext} (p : Elementary Γ) :
      Derivation ((p ∨ₚ p) ⊃ₚ p)
  /-- ✱1·3. Principle of addition (`Add`). -/
  | star_1_3 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation (q ⊃ₚ (p ∨ₚ q))

notation:45 "⊢ₚ " p => Derivation p

end PM
