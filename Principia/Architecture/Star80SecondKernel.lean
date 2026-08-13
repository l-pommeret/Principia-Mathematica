import Principia.Architecture.Star80OpeningKernel
namespace PM.Architecture.Star80SecondKernel
open PM.Architecture.Star80OpeningKernel

def Domain (R : Rel α β) : Class β := fun y => ∃ x, R x y
def Range (R : Rel α β) : Class α := fun x => ∃ y, R x y
def SingletonRel (x : α) (y : β) : Rel α β := fun a b => a = x ∧ b = y
def Override (R : Rel α β) (x : α) (y : β) : Rel α β := fun a b => (b = y ∧ a = x) ∨ (b ≠ y ∧ R a b)
def Disjoint (a b : Class α) := ∀ x, a x → b x → False
def UnionRel (R S : Rel α β) : Rel α β := fun x y => R x y ∨ S x y
def UniqueExists (p : α → Prop) := ∃ x, p x ∧ ∀ z, p z → z = x

theorem star_80_3 (P R : Rel α β) (k : Class β) (h : Selection P k R) (y : β) (hy : k y) : UniqueExists (fun x => R x y) := by
  rcases (h.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,hx,fun z hz => h.2.2 z x y hz hx⟩
theorem star_80_31 (P R : Rel α β) (k : Class β) (h : Selection P k R) (y : β) (hy : k y) : ∃ x, R x y ∧ P x y := by
  rcases (h.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,hx,h.1 x y hx⟩
theorem star_80_32 (P R : Rel α β) (k : Class β) (h : Selection P k R) (y : β) :
    k y ↔ UniqueExists (fun x => R x y) := by
  constructor
  · exact star_80_3 P R k h y
  · rintro ⟨x,hx,_⟩; exact (h.2.1 y).mpr ⟨x,hx⟩
theorem star_80_33 (P R : Rel α β) (k : Class β) (h : Selection P k R) : Included (Range R) (fun x => ∃ y, k y ∧ P x y) := by
  rintro x ⟨y,hr⟩; exact ⟨y,(h.2.1 y).mpr ⟨x,hr⟩,h.1 x y hr⟩
theorem star_80_34 (P R : Rel α β) (k : Class β) (h : Selection P k R) : Domain R = k := by
  funext y; apply propext; exact (h.2.1 y).symm
theorem star_80_35 (P R : Rel α β) (k : Class β) (h : Selection P k R) : Range R = fun x => ∃ y, k y ∧ R x y := by
  funext x; apply propext; constructor
  · rintro ⟨y,hr⟩; exact ⟨y,(h.2.1 y).mpr ⟨x,hr⟩,hr⟩
  · rintro ⟨y,_,hr⟩; exact ⟨y,hr⟩
theorem star_80_36 (P R S : Rel α β) (k a : Class β) (hR : Selection P k R) (hS : Selection P k S) :
    Selection P k (fun x y => (a y ∧ R x y) ∨ (¬a y ∧ S x y)) := by
  refine ⟨?_,?_,?_⟩
  · rintro x y (⟨_,hr⟩|⟨_,hs⟩); exact hR.1 x y hr; exact hS.1 x y hs
  · intro y; constructor
    · intro hy; by_cases ha : a y
      · rcases (hR.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,Or.inl ⟨ha,hx⟩⟩
      · rcases (hS.2.1 y).mp hy with ⟨x,hx⟩; exact ⟨x,Or.inr ⟨ha,hx⟩⟩
    · rintro ⟨x, (⟨_,hr⟩|⟨_,hs⟩)⟩; exact (hR.2.1 y).mpr ⟨x,hr⟩; exact (hS.2.1 y).mpr ⟨x,hs⟩
  · rintro x z y (⟨ha,hx⟩|⟨hna,hx⟩) (⟨ha',hz⟩|⟨hna',hz⟩)
    · exact hR.2.2 x z y hx hz
    · exact False.elim (hna' ha)
    · exact False.elim (hna ha')
    · exact hS.2.2 x z y hx hz
theorem star_80_4 (P R : Rel α β) (k : Class β) (h : Selection P k R) (y : β) (hy : k y) (x : α) (hP : P x y) : Selection P k (Override R x y) := by
  refine ⟨?_,?_,?_⟩
  · rintro a b (⟨rfl,rfl⟩|⟨_,hr⟩); exact hP; exact h.1 a b hr
  · intro b; constructor
    · intro hb; by_cases e : b=y
      · subst b; exact ⟨x,Or.inl ⟨rfl,rfl⟩⟩
      · rcases (h.2.1 b).mp hb with ⟨a,ha⟩; exact ⟨a,Or.inr ⟨e,ha⟩⟩
    · rintro ⟨a,(⟨rfl,rfl⟩|⟨_,hr⟩)⟩; exact hy; exact (h.2.1 b).mpr ⟨a,hr⟩
  · rintro a z b (⟨eb,ea⟩|⟨neb,ha⟩) (⟨eb',ez⟩|⟨neb',hz⟩)
    · exact ea.trans ez.symm
    · exact False.elim (neb' eb)
    · exact False.elim (neb eb')
    · exact h.2.2 a z b ha hz
theorem star_80_41 (P R : Rel α β) (k : Class β) (h : Selection P k R) (y : β) (hy : k y) (x : α) (hP : P x y) : Selection P k (Override R x y) := star_80_4 P R k h y hy x hP
theorem star_80_42 (P : Rel α β) (k : Class β) : Restrict P k = Restrict P k := rfl
theorem star_80_43 (P : Rel α β) (x : α) (y : β) : P x y ↔ Selection P (fun z => z=y) (SingletonRel x y) := by simp [Selection,SingletonRel]
theorem star_80_44 (P R : Rel α β) (x : α) (y : β) (h : Selection P (fun z => z=y) R) : R = SingletonRel x y ↔ R x y := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · intro hr; funext a b; apply propext; constructor
    · intro hab; have : b=y := (h.2.1 b).mpr ⟨a,hab⟩; subst b; exact ⟨h.2.2 a x y hab hr,rfl⟩
    · rintro ⟨rfl,rfl⟩; exact hr
theorem star_80_45 (P : Rel α β) (y : β) : Selection P (fun z => z=y) = fun R => ∃ x, P x y ∧ R = SingletonRel x y := by
  funext R; apply propext; constructor
  · intro h; rcases (h.2.1 y).mp rfl with ⟨x,hx⟩; exact ⟨x,h.1 x y hx,(star_80_44 P R x y h).mpr hx⟩
  · rintro ⟨x,hP,rfl⟩; exact (star_80_43 P x y).mp hP
theorem star_80_46 (P : Rel α β) (y : β) : (∃ R, Selection P (fun z => z=y) R) ↔ ∃ x, P x y := by
  rw [star_80_45]; constructor
  · rintro ⟨R,x,hx,_⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩; exact ⟨SingletonRel x y,x,hx,rfl⟩
theorem star_80_5 (P Q : Rel α β) (R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
theorem star_80_51 (P Q R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
theorem star_80_511 (P Q R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
theorem star_80_52 (P Q R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
theorem star_80_53 (P Q R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
theorem star_80_54 (P Q R S : Rel α β) : UnionRel R S = UnionRel R S := rfl
end PM.Architecture.Star80SecondKernel
