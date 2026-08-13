import Principia.Architecture.Star256OpeningKernel
namespace PM.Architecture.Star256MiddleKernel
open PM.Architecture.Star256OpeningKernel
universe u v
def UnionOne (c : Class α) (one : α) : Class α := fun x => c x ∨ x = one
def RemoveOne (c : Class α) (one : α) : Class α := fun x => c x ∧ x ≠ one
def Image (f : α → β) (c : Class α) : Class β := fun y => ∃ x, c x ∧ f x = y
def RelHom (R : Rel α) (S : Rel β) (f : α → β) := ∀ a b, R a b → S (f a) (f b)

theorem star_256_4 (c : Class α) (h : ∃ x, c x) : ¬(∀ x, ¬c x) := by rintro hn; rcases h with ⟨x,hx⟩; exact hn x hx
theorem star_256_41 (c : Class α) (one : α) : UnionOne c one = fun x => c x ∨ x = one := rfl
theorem star_256_411 (c : Class α) (one : α) : c one → UnionOne c one one := fun h => Or.inl h
theorem star_256_413 (c : Class α) (one x : α) : UnionOne c one x → c x ∨ x = one := fun h => h
theorem star_256_414 (c : Class α) (one x : α) : c x → UnionOne c one x := fun h => Or.inl h
theorem star_256_42 (c : Class α) (one : α) : RemoveOne (UnionOne c one) one = fun x => (c x ∨ x = one) ∧ x ≠ one := rfl
theorem star_256_421 (c : Class α) (one x : α) : c x → UnionOne c one x := fun h => Or.inl h
theorem star_256_422 (c : Class α) (one x : α) : RemoveOne c one x → c x := fun h => h.1
theorem star_256_43 (c : Class α) (one x : α) : RemoveOne c one x ↔ c x ∧ x ≠ one := Iff.rfl
theorem star_256_5 (f : α → β) (c : Class α) (x : α) : c x → Image f c (f x) := fun h => ⟨x,h,rfl⟩
theorem star_256_51 (R : Rel α) (S : Rel β) (f : α → β) (h : RelHom R S f) : RelHom R S f := h
theorem star_256_52 (f : α → β) (c : Class α) (y : β) : Image f c y → ∃ x, c x ∧ f x = y := fun h => h
theorem star_256_53 (R : Rel α) (S : Rel β) (f : α → β) (a b : α) (h : RelHom R S f) : R a b → S (f a) (f b) := h a b
theorem star_256_54 (f : α → β) (c : Class α) : Image f c = fun y => ∃ x, c x ∧ f x = y := rfl
theorem star_256_55 (f : α → β) (c : Class α) (x : α) (hx : c x) : Image f c (f x) := ⟨x,hx,rfl⟩
end PM.Architecture.Star256MiddleKernel
