import Principia.Architecture.Star212ExistenceKernel
namespace PM.Architecture.Star212MorphismsKernel
open PM.Architecture.Star212OpeningKernel PM.Architecture.Star212MiddleKernel PM.Architecture.Star212OrderKernel PM.Architecture.Star212LimitsKernel PM.Architecture.Star212ExistenceKernel
universe u v
def Image (f : α → β) (c : Class α) : Class β := fun y => ∃ x, c x ∧ f x = y
def RelHom (R : Rel α) (S : Rel β) (f : α → β) := ∀ a b, R a b → S (f a) (f b)
def InjectiveOn (c : Class α) (f : α → β) := ∀ a b, c a → c b → f a = f b → a = b

theorem star_212_653 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : HasGreatest R c := ⟨x,h⟩
theorem star_212_66 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : Greatest R c x := h
theorem star_212_661 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : Least R c x := h
theorem star_212_662 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : c x := h.1
theorem star_212_663 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : ∀ y, c y → y = x ∨ R x y := h.2
theorem star_212_664 (R : Rel α) (c : Class α) : HasLeast R c ↔ ∃ x, Least R c x := Iff.rfl
theorem star_212_665 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : HasLeast R c := ⟨x,h⟩
theorem star_212_666 (R : Rel α) (c : Class α) : (∃ x, Least R c x) = HasLeast R c := rfl
theorem star_212_667 (c : Class (Class α)) : Dom (Sgm c) = Dom (Sigma c) := rfl
theorem star_212_7 (f : α → β) (c : Class α) : Image f c = fun y => ∃ x, c x ∧ f x = y := rfl
theorem star_212_701 (f : α → β) (c : Class α) (y : β) : Image f c y ↔ ∃ x, c x ∧ f x = y := Iff.rfl
theorem star_212_702 (f : α → β) (c d : Class α) :
    (∀ x, c x ↔ d x) → Image f c = Image f d := by intro h; funext y; apply propext; simp [Image,h]
theorem star_212_71 (R : Rel α) (S : Rel β) (f : α → β) (h : RelHom R S f) : RelHom R S f := h
theorem star_212_711 (R : Rel α) (S : Rel β) (f : α → β) (h : RelHom R S f) : ∀ a b, R a b → S (f a) (f b) := h
theorem star_212_712 (c : Class (Class α)) (d : Class (Class β)) (f : Class α → Class β)
    (h : RelHom (Sgm c) (Sgm d) f) : RelHom (Sgm c) (Sgm d) f := h
theorem star_212_72 (c : Class (Class α)) (d : Class (Class β)) (f : Class α → Class β)
    (hs : RelHom (Sigma c) (Sigma d) f) (hg : RelHom (Sgm c) (Sgm d) f) :
    RelHom (Sigma c) (Sigma d) f ∧ RelHom (Sgm c) (Sgm d) f := ⟨hs,hg⟩
end PM.Architecture.Star212MorphismsKernel
