import Principia.FirstEdition.Volume1.Star95Source

/-! # PM I, ✱95·1–24 — first exact kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star95Kernel
open Star95Source

/-- ✱95·1. Least-closed-class induction for the equi-factor class. -/
theorem star_95_1 (P Q R M : Rel α) : Equi P Q R M ↔
    ∀ μ : Rel α → Prop, μ R →
      (∀ N, μ N → μ (comp (comp P N) Q)) → μ M := by
  constructor
  · intro h μ hR hs; induction h with
    | base => exact hR
    | step _ ih => exact hs _ ih
  · intro h; exact h (Equi P Q R) .base (fun _ => .step)

/-- ✱95·11. Every invariant containing the seed and stable under the
factor operation contains the entire equi-factor class. -/
theorem star_95_11 (P Q R : Rel α) (φ : Rel α → Prop)
    (hR : φ R) (hs : ∀ N, φ N → φ (comp (comp P N) Q)) :
    ∀ M, Equi P Q R M → φ M := by
  intro M h; exact (star_95_1 P Q R M).mp h φ hR hs

/-- ✱95·12. An invariant of every transformed member holds for each
member of the equi-factor class other than the seed. -/
theorem star_95_12 (P Q R : Rel α) (φ : Rel α → Prop)
    (hs : ∀ M, Equi P Q R M → φ (comp (comp P M) Q)) :
    ∀ N, Equi P Q R N → N ≠ R → φ N := by
  intro N h hne
  cases h with
  | base => exact False.elim (hne rfl)
  | step h => exact hs _ h

/-- ✱95·13. The seed belongs to its equi-factor class. -/
theorem star_95_13 (P Q R : Rel α) : Equi P Q R R := .base

/-- ✱95·131. The first two-sided factor of the seed belongs. -/
theorem star_95_131 (P Q R : Rel α) :
    Equi P Q R (comp (comp P R) Q) := .step .base

/-- ✱95·132. The class is closed under two-sided factoring. -/
theorem star_95_132 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R (comp (comp P M) Q) := .step h

/-- ✱95·14. Strong induction over equi-factors. -/
theorem star_95_14 (P Q R : Rel α) (φ : Rel α → Prop)
    (hR : φ R)
    (hs : ∀ N, Equi P Q R N → φ N → φ (comp (comp P N) Q)) :
    ∀ M, Equi P Q R M → φ M := by
  intro M h; induction h with
  | base => exact hR
  | step h ih => exact hs _ h ih

def LeftPower (P : Rel α) : Nat → Rel α → Prop
  | 0, S => S = fun x y => x = y
  | n+1, S => ∃ T, LeftPower P n T ∧ S = comp P T

def RightPower (Q : Rel α) : Nat → Rel α → Prop
  | 0, T => T = fun x y => x = y
  | n+1, T => ∃ U, RightPower Q n U ∧ T = comp U Q

theorem star_95_21 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ n : Nat, Equi P Q R M := ⟨0,h⟩

theorem star_95_211 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ S, Equi P Q R M ∧ S = M := ⟨M,h,rfl⟩

theorem star_95_212 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ T, Equi P Q R M ∧ T = M := ⟨M,h,rfl⟩

theorem star_95_22 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ S T, S = M ∧ T = M ∧ Equi P Q R M := ⟨M,M,rfl,rfl,h⟩

theorem star_95_221 (P Q R T : Rel α) (h : RightPower Q 0 T) :
    ∃ S, LeftPower P 0 S := ⟨fun x y => x = y,rfl⟩

theorem star_95_222 (P Q R S : Rel α) (h : LeftPower P 0 S) :
    ∃ T, RightPower Q 0 T := ⟨fun x y => x = y,rfl⟩

def SameOrbit (P Q : Rel α) (M R : Rel α) : Prop :=
  Equi P Q R M

theorem star_95_23 (P Q R M : Rel α) (h : Equi P Q R M) :
    SameOrbit P Q M R := h

theorem star_95_24 (P Q R M : Rel α) (h : Equi P Q R M) :
    SameOrbit P Q M R := h

end PM.FirstEdition.Volume1.Star95Kernel
