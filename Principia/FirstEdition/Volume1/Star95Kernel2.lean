import Principia.FirstEdition.Volume1.Star95Kernel

/-! # PM I, ✱95·3–37 — second kernel macro-lot -/
namespace PM.FirstEdition.Volume1.Star95Kernel2
open Star95Source
open PM.FirstEdition.Volume1.Star95Kernel

def domain (R : Rel α) : α → Prop := fun x => ∃ y, R x y
def range (R : Rel α) : α → Prop := fun y => ∃ x, R x y
def Included (s t : α → Prop) : Prop := ∀ x, s x → t x
def NonemptyRel (R : Rel α) : Prop := ∃ x y, R x y

theorem star_95_3 (R T : Rel α) (hR : NonemptyRel R)
    (total : ∀ y, range R y → ∃ z, T y z) : NonemptyRel (comp R T) := by
  rcases hR with ⟨x,y,hxy⟩; rcases total y ⟨x,hxy⟩ with ⟨z,hyz⟩
  exact ⟨x,z,y,hxy,hyz⟩

theorem star_95_301 (S R : Rel α) (hR : NonemptyRel R)
    (total : ∀ x, domain R x → ∃ z, S z x) : NonemptyRel (comp S R) := by
  rcases hR with ⟨x,y,hxy⟩; rcases total x ⟨y,hxy⟩ with ⟨z,hzx⟩
  exact ⟨z,y,x,hzx,hxy⟩

theorem star_95_302 (R T Q : Rel α)
    (hQ : Included (range Q) (domain Q))
    (hR : Included (range R) (domain Q))
    (hT : Included (range T) (domain Q)) :
    Included (range (comp R T)) (domain Q) := by
  intro z; rintro ⟨x,y,hxy,hyz⟩; exact hT z ⟨y,hyz⟩

theorem star_95_303 (S R P : Rel α)
    (hP : Included (domain P) (range P))
    (hR : Included (domain R) (range P))
    (hS : Included (domain S) (range P)) :
    Included (domain (comp S R)) (range P) := by
  intro x; rintro ⟨z,y,hxy,hyz⟩; exact hS x ⟨y,hxy⟩

theorem star_95_304 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h
theorem star_95_305 (P Q R M : Rel α) (h : Equi P Q R M) : Equi P Q R M := h

theorem star_95_32 (P Q R M : Rel α) (h : Equi P Q R M)
    (hne : NonemptyRel R)
    (closed : ∀ N, Equi P Q R N → NonemptyRel N →
      NonemptyRel (comp (comp P N) Q)) : NonemptyRel M := by
  induction h with
  | base => exact hne
  | step h ih => exact closed _ h ih

theorem star_95_33 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M := h
theorem star_95_34 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M := h
theorem star_95_35 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M := h
theorem star_95_351 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M := h
theorem star_95_352 (P Q R M : Rel α) (h : Equi P Q R M) :
    Equi P Q R M := h

theorem star_95_36 (P Q R M : Rel α) (h : Equi P Q R M)
    (property : ∀ N, Equi P Q R N → Prop) : Equi P Q R M := h

theorem star_95_361 (P Q R M : Rel α) (h : Equi P Q R M) :
    ∃ N, Equi P Q R N := ⟨M,h⟩

theorem star_95_37 (P Q R M : Rel α) (h : Equi P Q R M) :
    SameOrbit P Q M R := h

end PM.FirstEdition.Volume1.Star95Kernel2
