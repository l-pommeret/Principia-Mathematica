import Principia.Syntax.Formula

namespace PM

/-- Assertion in the reconstructed elementary PM calculus.

`Derivation [] p` represents assertion of a definite proposition. For nonempty
`Γ`, `Derivation Γ p` represents assertion of an elementary propositional
function with real variables; members of `Γ` are not hypotheses.

The formula parameters of the primitive propositions provide schematic Lean
instantiation for PM's printed substitutions. That metalinguistic convention is
not a constructor of this inductive type and is distinct both from ✱1·1/✱1·11
and from capture-free object-syntactic substitution under the binders of ✱9.
See `docs/SUBSTITUTION.md`. -/
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
  /-- ✱1·4. Principle of permutation (`Perm`). -/
  | star_1_4 {Γ : RealContext} (p q : Elementary Γ) :
      Derivation ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p))
  /-- ✱1·5. Associative principle (`Assoc`). -/
  | star_1_5 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r)))
  /-- ✱1·6. Principle of summation (`Sum`). -/
  | star_1_6 {Γ : RealContext} (p q r : Elementary Γ) :
      Derivation ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)))

notation:45 "⊢ₚ " p => Derivation p

namespace Derivation

/-! ## Uniform metalinguistic detachment

The following is an editorial interface lemma, not a proposition printed in
PM.  It combines, without identifying them, the two primitive rules printed in
the first edition, volume I:

* ✱1·1, p. 98: “Anything implied by a true elementary proposition is true.”
* ✱1·11, p. 99: the corresponding assertion rule for an elementary
  propositional function with one or more real variables.

The shape of `Γ` records precisely which historical rule applies.  It is not a
context of logical hypotheses.
-/

/-- Metalinguistic detachment, uniform in the real-variable context `Γ`.

For `Γ = []` this is exactly ✱1·1.  For `Γ = τ :: Δ` this is exactly ✱1·11,
with only the structural witness that the real-variable context is nonempty.
-/
theorem detach {Γ : PM.RealContext} {φ ψ : PM.Elementary Γ}
    (hφ : PM.Derivation φ) (hφψ : PM.Derivation (φ ⊃ₚ ψ)) :
    PM.Derivation ψ := by
  match Γ, φ, ψ, hφ, hφψ with
  | [], φ, ψ, hφ, hφψ => exact PM.Derivation.star_1_1 hφ hφψ
  | (τ :: Δ), φ, ψ, hφ, hφψ =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hφ hφψ

end Derivation

end PM
