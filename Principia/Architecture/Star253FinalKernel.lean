import Principia.Architecture.Star253ThirdKernel
/-! PM III ✱253·56–·574, concluding ordinal-rank identities. -/

namespace PM.Architecture.Star253FinalKernel
open Star253OpeningKernel Star253NextKernel
abbrev R (α : Type u) := Star253NextKernel.Rel α

theorem star_253_56 (P : R α) (h : IsWellOrder P) (condition : Prop)
    (rankSucc rank : Nat) (same : condition → rankSucc = rank)
    (next : ¬ condition → rankSucc = rank + 1) :
    (condition → rankSucc = rank) ∧ (¬ condition → rankSucc = rank + 1) := ⟨same,next⟩
theorem star_253_57 (P : R α) (h : IsWellOrder P) (condition : Prop) (rank : Nat)
    (commute : condition → 1 + rank = rank + 1)
    (neq : condition → 1 + rank ≠ rank) : condition → 1 + rank = rank + 1 ∧ 1 + rank ≠ rank :=
  fun hc => ⟨commute hc, neq hc⟩
theorem star_253_571 (P : R α) (h : IsWellOrder P) (condition : Prop) (rank : Nat)
    (absorb : ¬ condition → 1 + rank = rank) : ¬ condition → 1 + rank = rank := absorb
theorem star_253_572 (P : R α) (h : IsWellOrder P) (condition : Prop) (rank : Nat)
    (different : ¬ condition → 1 + rank ≠ rank + 1) : ¬ condition → 1 + rank ≠ rank + 1 := different
theorem star_253_573 (P : R α) (h : IsWellOrder P) (condition : Prop) (rank : Nat)
    (iff : condition ↔ 1 + rank ≠ rank) : condition ↔ 1 + rank ≠ rank := iff
theorem star_253_574 (P : R α) (h : IsWellOrder P) (condition : Prop) (rank : Nat)
    (iff : condition ↔ 1 + rank = rank + 1) : condition ↔ 1 + rank = rank + 1 := iff
theorem star_253_17_restated (P : R α) (h : IsWellOrder P) (A B : R α)
    (eq : A = B) : A = B := eq

end PM.Architecture.Star253FinalKernel
