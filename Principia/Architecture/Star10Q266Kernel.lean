import Principia.Architecture.Star925Kernel
import Principia.Architecture.Star96SameType

/-!
# PM I ✱10·12

The printed proposition is explicitly cited as ✱9·25 and has the identical
ordered target.  This module exposes that exact closed judgement under its
✱10 number; it introduces no conversion or assertion constructor.
-/

namespace PM.FirstEdition.Volume1.Star10

open PM
open PM.Architecture.FirstOrderPrerequisites

/-- PM I (1910), p. 146, ✱10·12: `⊢ : .(x).p ∨ φx .⊃ : p .∨ .(x).φx`. -/
theorem star_10_12 (p : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) :
    PM.Architecture.Star925Kernel.Star925KernelAssertion p φ :=
  PM.Architecture.Star925Kernel.derive p φ

/-- Structural occurrence of the newly leading real argument.  This is local
to ✱10·121 and is not a generic significance/inference rule. -/
private def significantRealHead : Apparent (.elementaryProposition :: Γ) Δ → Bool
  | .constant _ => false
  | .real .zero => true
  | .real (.succ _) => false
  | .bound _ => false
  | .neg proposition => significantRealHead proposition
  | .disj left right => significantRealHead left || significantRealHead right

private def RealHeadSignificant
    (proposition : Apparent (.elementaryProposition :: Γ) Δ) : Prop :=
  significantRealHead proposition = true

/-- PM I (1910), p. 146, ✱10·121.  Opening the apparent argument `x` as a
fresh real argument `a` of the same assigned elementary-proposition type
preserves and reflects its structural significance. -/
theorem star_10_121
    (φ : Apparent Γ (.elementaryProposition :: Δ)) :
    Apparent.Significant (.zero : BoundVar
        (.elementaryProposition :: Δ) .elementaryProposition) φ ↔
      RealHeadSignificant (Apparent.openRealHead φ) := by
  induction φ with
  | constant name => rfl
  | real v => cases v <;> rfl
  | bound v => cases v <;> rfl
  | neg proposition ih => exact ih
  | disj left right ihLeft ihRight =>
      simp only [Apparent.Significant, Apparent.significant,
        RealHeadSignificant] at ihLeft ihRight ⊢
      change (_ || _) = true ↔
        (significantRealHead (Apparent.openRealHead left) ||
          significantRealHead (Apparent.openRealHead right)) = true
      simpa only [Bool.or_eq_true, ihLeft, ihRight]

end PM.FirstEdition.Volume1.Star10
