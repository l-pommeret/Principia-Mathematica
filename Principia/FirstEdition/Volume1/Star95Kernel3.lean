import Principia.FirstEdition.Volume1.Star95Kernel2

/-! # PM I, ✱95·38–471 — third kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star95Kernel3
open Star95Source
open PM.FirstEdition.Volume1.Star95Kernel
open PM.FirstEdition.Volume1.Star95Kernel2

theorem star_95_38 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h
theorem star_95_381 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h
theorem star_95_382 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h
theorem star_95_383 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h

def ClosedClass (P Q : Rel α) (μ : Rel α → Prop) : Prop :=
  ∀ N, μ N → μ (comp (comp P N) Q)

theorem star_95_4 (P Q R : Rel α) :
    ClosedClass P Q (Equi P Q R) := fun _ h => .step h

theorem star_95_41 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R (comp (comp P M) Q) := .step h

theorem star_95_411 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ N, Equi P Q R N ∧ N = comp (comp P M) Q := ⟨_,.step h,rfl⟩

theorem star_95_42 (P Q R : Rel α) : Equi P Q R R := .base

theorem star_95_43 (P Q R M : Rel α) (h : Equi P Q R M) :
    SameOrbit P Q M R := h

theorem star_95_431 (P Q R M : Rel α) (h : SameOrbit P Q M R) :
    Equi P Q R M := h

theorem star_95_44 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∀ μ, μ R → ClosedClass P Q μ → μ M :=
  (star_95_1 P Q R M).mp h

theorem star_95_45 (P Q R M : Rel α)
    (h : ∀ μ, μ R → ClosedClass P Q μ → μ M) : Equi P Q R M :=
  (star_95_1 P Q R M).mpr h

theorem star_95_46 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M ∧ SameOrbit P Q M R := ⟨h,h⟩

theorem star_95_47 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ μ, μ R ∧ ClosedClass P Q μ ∧ μ M := ⟨Equi P Q R,.base,star_95_4 P Q R,h⟩

theorem star_95_471 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ N, Equi P Q R N := ⟨M,h⟩

end PM.FirstEdition.Volume1.Star95Kernel3
