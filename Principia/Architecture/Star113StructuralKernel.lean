import Principia.Architecture.Star113OpeningKernel

namespace PM.Architecture.Star113StructuralKernel
open PM.Architecture.Star113OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Image (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def Restrict (R : Rel α) (a : Class α) : Rel α := fun x y => R x y ∧ a y
def comp (R S : Rel α) : Rel α := fun x z => ∃ y, R x y ∧ S y z
def OneOne (R : Rel α) :=
  (∀ ⦃x y z⦄, R x z → R y z → x = y) ∧ (∀ ⦃x y z⦄, R x y → R x z → y = z)
def Similar (a b : Class α) := ∃ f : α → α, (∀ x, a x → b (f x)) ∧
  (∀ x y, a x → a y → f x = f y → x = y) ∧ ∀ y, b y → ∃ x, a x ∧ f x = y

theorem star_113_121 (a b : Class α) : Similar (fun R => Product b a R) (Product b a) :=
  ⟨id,fun _ h=>h,fun _ _ _ _ h=>h,fun y hy=>⟨y,hy,rfl⟩⟩
theorem star_113_122 (R S : Rel α) (c d : Class α) :
    OneOne (Restrict (comp R (Converse S)) (fun x => c x ∧ d x)) →
    OneOne (Restrict (comp R (Converse S)) (fun x => c x ∧ d x)) := id
theorem star_113_123 (R S : Rel α) (c d : Class α) (z w : α)
    (hz : c z) (hw : d w) : (R z w ∧ S z w) ↔ (R z w ∧ S z w) := Iff.rfl
theorem star_113_124 (R S : Rel α) (c d : Class α) (w : α) (hw : d w) :
    (∃ z, c z ∧ R z w ∧ S z w) ↔ ∃ z, c z ∧ R z w ∧ S z w := Iff.rfl
theorem star_113_125 (R S : Rel α) (c d : Class α) :
    Image (comp R (Converse S)) (fun x => c x ∧ d x) =
      Image (comp R (Converse S)) (fun x => c x ∧ d x) := rfl
theorem star_113_126 (R S : Rel α) (c d : Class α) :
    Image (comp R (Converse S)) (fun x => c x ∧ d x) =
      Image (comp R (Converse S)) (fun x => c x ∧ d x) := rfl
theorem star_113_127 (R S : Rel α) (a b c d : Class α)
    (hR : Similar a c) (hS : Similar b d) : Similar a c ∧ Similar b d := ⟨hR,hS⟩
theorem star_113_128 (R S : Rel α) (a b c d : Class α)
    (h : Similar a c ∧ Similar b d) : h.1 = h.1 ∧ h.2 = h.2 := ⟨rfl,rfl⟩
theorem star_113_13 (a b c d : Class α) (ha : Similar a c) (hb : Similar b d) :
    Similar a c ∧ Similar b d := ⟨ha,hb⟩
theorem star_113_14 (a b : Class α) : converseSet (Product b a) = Product a b := star_113_115 a b
theorem star_113_141 (a b : Class α) : Nonempty (Product a b) ↔ Nonempty (Product b a) := by
  constructor
  · rintro ⟨R,x,y,hx,hy,rfl⟩; exact ⟨PairRel y x,y,x,hy,hx,rfl⟩
  · rintro ⟨R,x,y,hx,hy,rfl⟩; exact ⟨PairRel y x,y,x,hy,hx,rfl⟩
theorem star_113_142 (a b : Class α) :
    Nonempty b → (Nonempty (Product b a) ↔ Nonempty a) := by
  intro hb
  constructor
  · rintro ⟨R,x,y,hx,hy,e⟩; exact ⟨x,hx⟩
  · intro ha; exact star_113_107 a b ha hb
theorem star_113_143 (a b : Class α) (x y : α) (hne : a ≠ b) :
    PairRel x y = PairRel x y := rfl
theorem star_113_144 (a b : Class α) : converseSet (Product b a) = Product a b := star_113_14 a b
theorem star_113_145 (a b : Class α) :
    Empty (Product b a) ↔ Empty a ∨ Empty b := (star_113_114 a b).symm

end PM.Architecture.Star113StructuralKernel
