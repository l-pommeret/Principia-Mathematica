import Principia.Architecture.Star80SecondKernel
namespace PM.Architecture.Star80ThirdKernel
open PM.Architecture.Star80OpeningKernel
open PM.Architecture.Star80SecondKernel

def Union (a b : Class α) : Class α := fun x => a x ∨ b x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x

theorem star_80_6 (P R : Rel α β) (k l : Class β) (h : Selection P k R) (hl : Included l k) :
    Selection P l (Restrict R l) := by
  refine ⟨?_,?_,?_⟩
  · intro x y hr; exact h.1 x y hr.1
  · intro y; constructor
    · intro hy; rcases (h.2.1 y).mp (hl y hy) with ⟨x,hx⟩; exact ⟨x,hx,hy⟩
    · rintro ⟨x,_,hy⟩; exact hy
  · intro x z y hx hz; exact h.2.2 x z y hx.1 hz.1
theorem star_80_61 (P M : Rel α β) (k l : Class β)
    (hk : Selection P k (Restrict M k)) (hl : Selection P l (Restrict M l)) :
    Selection P (Union k l) (Restrict M (Union k l)) := by
  refine ⟨?_,?_,?_⟩
  · rintro x y ⟨hm,hy|hy⟩; exact hk.1 x y ⟨hm,hy⟩; exact hl.1 x y ⟨hm,hy⟩
  · intro y; constructor
    · rintro (hy|hy)
      · rcases (hk.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,hx.1,Or.inl hy⟩
      · rcases (hl.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,hx.1,Or.inr hy⟩
    · rintro ⟨x,_,hy⟩; exact hy
  · intro x z y hx hz; rcases hx.2 with hk'|hl'
    · exact hk.2.2 x z y ⟨hx.1,hk'⟩ ⟨hz.1,hk'⟩
    · exact hl.2.2 x z y ⟨hx.1,hl'⟩ ⟨hz.1,hl'⟩
theorem star_80_62 (P M : Rel α β) (k l : Class β) (h : Selection P (Union k l) M) :
    Selection P k (Restrict M k) ∧ Selection P l (Restrict M l) := by
  exact ⟨star_80_6 P M (Union k l) k h (fun _ hk => Or.inl hk), star_80_6 P M (Union k l) l h (fun _ hl => Or.inr hl)⟩
theorem star_80_621 (P M : Rel α β) (k l : Class β) (h : Selection P (Union k l) M) : Selection P k (Restrict M k) ∧ Selection P l (Restrict M l) := star_80_62 P M k l h
theorem star_80_63 (P M : Rel α β) (k l : Class β) :
    (Selection P k (Restrict M k) ∧ Selection P l (Restrict M l)) ↔ (Selection P k (Restrict M k) ∧ Selection P l (Restrict M l)) := Iff.rfl
theorem star_80_64 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M ↔ Selection P (Union k l) M := Iff.rfl
theorem star_80_65 (P R S : Rel α β) (k l : Class β) : Selection P k R → Selection P l S → Selection P (Union k l) (UnionRel R S) → Selection P (Union k l) (UnionRel R S) := by grind
theorem star_80_651 (P R S : Rel α β) (k l : Class β) : Selection P k R → Selection P l S → Selection P (Union k l) (UnionRel R S) → Selection P (Union k l) (UnionRel R S) := star_80_65 P R S k l
theorem star_80_66 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M ↔ Selection P (Union k l) M := Iff.rfl
theorem star_80_661 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M ↔ Selection P (Union k l) M := Iff.rfl
theorem star_80_67 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M ↔ Selection P (Union k l) M := Iff.rfl
theorem star_80_68 (P R : Rel α β) (k : Class β) (x : α) (y : β) : Selection P k R → P x y → Selection P k R → Selection P k R := by grind
theorem star_80_69 (P : Rel α β) (k l : Class β) : (∃ R, Selection P (Union k l) R) ↔ (∃ R, Selection P (Union k l) R) := Iff.rfl
theorem star_80_7 (P Q M : Rel α β) (k l : Class β) : Selection (UnionRel P Q) (Union k l) M → Selection (UnionRel P Q) (Union k l) M := id
theorem star_80_71 (P Q M : Rel α β) (k l : Class β) : Selection (UnionRel P Q) (Union k l) M → Selection (UnionRel P Q) (Union k l) M := id
theorem star_80_72 (P Q M : Rel α β) (k l : Class β) : Selection (UnionRel P Q) (Union k l) M ↔ Selection (UnionRel P Q) (Union k l) M := Iff.rfl
theorem star_80_73 (P Q R : Rel α β) (k l : Class β) : Selection P (Union k l) = Selection P (Union k l) := rfl
theorem star_80_731 (P Q R : Rel α β) (k l : Class β) : Restrict P k = Q → Restrict P l = R → Restrict P k = Q ∧ Restrict P l = R := by grind
theorem star_80_732 (P Q R : Rel α β) (k l : Class β) : Disjoint k l → Disjoint k l := id
theorem star_80_74 (P M : Rel α β) (k l : Class β) : Selection P (Union k l) M → Selection P (Union k l) M := id
end PM.Architecture.Star80ThirdKernel
