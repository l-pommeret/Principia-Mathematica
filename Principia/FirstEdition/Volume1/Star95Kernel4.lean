import Principia.FirstEdition.Volume1.Star95Kernel3

/-! # PM I, ✱95·51–7 — final numbered propositions -/
namespace PM.FirstEdition.Volume1.Star95Kernel4
open Star95Source
open PM.FirstEdition.Volume1.Star95Kernel
open PM.FirstEdition.Volume1.Star95Kernel2
open PM.FirstEdition.Volume1.Star95Kernel3

theorem star_95_51 (P Q R M : Rel α) (h : Equi P Q R M) :
    SameOrbit P Q M R := h

theorem star_95_511 (P Q R M : Rel α) (h : SameOrbit P Q M R) :
    Equi P Q R M := h

def OrbitClass (P Q R : Rel α) : Rel α → Prop := Equi P Q R

theorem star_95_6 (P Q R M : Rel α) :
    OrbitClass P Q R M ↔ Equi P Q R M := Iff.rfl

theorem star_95_601 (P Q R : Rel α) : OrbitClass P Q R R := .base

theorem star_95_61 (P Q R M : Rel α) (h : OrbitClass P Q R M) :
    OrbitClass P Q R (comp (comp P M) Q) := .step h

theorem star_95_62 (P Q R : Rel α) :
    ClosedClass P Q (OrbitClass P Q R) := fun _ h => .step h

theorem star_95_64 (P Q R M : Rel α) (h : OrbitClass P Q R M) :
    ∀ μ, μ R → ClosedClass P Q μ → μ M :=
  (star_95_1 P Q R M).mp h

theorem star_95_7 (P Q R M : Rel α) :
    Equi P Q R M ↔ OrbitClass P Q R M := Iff.rfl

end PM.FirstEdition.Volume1.Star95Kernel4
