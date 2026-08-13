import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71DescriptionKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def image (R : Rel α) (a : Class α) : Class α := fun x => ∃ y, a y ∧ R x y
def converseImage (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def ExistsUnique (p : Class α) := ∃ x, p x ∧ ∀ y, p y → y = x

/-- PM I ✱71·32. -/
theorem star_71_32 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (ψ : Class α) (y : α) (hy : cod R y) :
    (ψ (f y) ↔ ∃ x, R x y ∧ ψ x) ∧ ((∃ x, R x y ∧ ψ x) ↔ ∀ x, R x y → ψ x) := by
  constructor
  · constructor
    · intro hp; exact ⟨f y,hf y hy,hp⟩
    · rintro ⟨x,hx,hp⟩; simpa [hR hx (hf y hy)] using hp
  · constructor
    · rintro ⟨x,hx,hp⟩ z hz; simpa [hR hz hx] using hp
    · intro h; exact ⟨f y,hf y hy,h _ (hf y hy)⟩
/-- PM I ✱71·321. -/
theorem star_71_321 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (ψ : Class α) (x : α) (hx : dom R x) :
    (ψ (f x) ↔ ∃ y, R x y ∧ ψ y) ∧ ((∃ y, R x y ∧ ψ y) ↔ ∀ y, R x y → ψ y) := by
  constructor
  · constructor
    · intro hp; exact ⟨f x,hf x hx,hp⟩
    · rintro ⟨y,hy,hp⟩; simpa [hR hy (hf x hx)] using hp
  · constructor
    · rintro ⟨y,hy,hp⟩ z hz; simpa [hR hz hy] using hp
    · intro h; exact ⟨f x,hf x hx,h _ (hf x hx)⟩
/-- PM I ✱71·33. -/
theorem star_71_33 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (ψ : Class α) (y : α) :
    cod R y → ((ψ (f y) ↔ ∃ x, R x y ∧ ψ x) ∧
      ((∃ x, R x y ∧ ψ x) ↔ ∀ x, R x y → ψ x)) := by
  intro hy; exact star_71_32 R f hR hf ψ y hy
/-- PM I ✱71·331, converse form of ·33. -/
theorem star_71_331 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (ψ : Class α) (x : α) (hx : dom R x) :
    (ψ (f x) ↔ ∃ y, R x y ∧ ψ y) ∧ ((∃ y, R x y ∧ ψ y) ↔ ∀ y, R x y → ψ y) :=
  star_71_321 R f hR hf ψ x hx
/-- PM I ✱71·332. -/
theorem star_71_332 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a : Class α) (y : α) (hy : cod R y) :
    a (f y) ↔ ExistsUnique (fun x => R x y ∧ a x) := by
  constructor
  · intro ha; exact ⟨f y,⟨hf y hy,ha⟩,fun z hz => hR hz.1 (hf y hy)⟩
  · rintro ⟨x,⟨hx,ha⟩,hu⟩; simpa [hR hx (hf y hy)] using ha
/-- PM I ✱71·333. -/
theorem star_71_333 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a : Class α) (x : α) (hx : dom R x) :
    a (f x) ↔ ExistsUnique (fun y => R x y ∧ a y) := by
  constructor
  · intro ha; exact ⟨f x,⟨hf x hx,ha⟩,fun z hz => hR hz.1 (hf x hx)⟩
  · rintro ⟨y,⟨hy,ha⟩,hu⟩; simpa [hR hy (hf x hx)] using ha
/-- PM I ✱71·34. -/
theorem star_71_34 (R S : Rel α) (f g : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (hg : ∀ y, cod S y → S (g y) y)
    (hrs : R = S) (y : α) (hy : cod R y) : f y = g y := by
  subst S; exact hR (hf y hy) (hg y hy)
/-- PM I ✱71·341. -/
theorem star_71_341 (R S : Rel α) (f g : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (hg : ∀ x, dom S x → S x (g x))
    (hrs : R = S) (x : α) (hx : dom R x) : f x = g x := by
  subst S; exact hR (hf x hx) (hg x hx)
/-- PM I ✱71·35. -/
theorem star_71_35 (R S : Rel α) (hR : OneMany R)
    (h : ∀ y, cod R y ∨ cod S y → (fun x => R x y) = fun x => S x y) : R = S := by
  funext x y; apply propext; constructor
  · intro hx; exact congrFun (h y (Or.inl ⟨x,hx⟩)) x ▸ hx
  · intro hx; exact congrFun (h y (Or.inr ⟨x,hx⟩)).symm x ▸ hx
/-- PM I ✱71·351. -/
theorem star_71_351 (R S : Rel α) (hR : ManyOne R)
    (h : ∀ x, dom R x ∨ dom S x → (fun y => R x y) = fun y => S x y) : R = S := by
  funext x y; apply propext; constructor
  · intro hy; exact congrFun (h x (Or.inl ⟨y,hy⟩)) y ▸ hy
  · intro hy; exact congrFun (h x (Or.inr ⟨y,hy⟩)).symm y ▸ hy
/-- PM I ✱71·352. -/
theorem star_71_352 (R S : Rel α) (hR : OneOne R)
    (hr : ∀ y, cod R y ∨ cod S y → (fun x => R x y) = fun x => S x y)
    (hl : ∀ x, dom R x ∨ dom S x → (fun y => R x y) = fun y => S x y) : R = S := by
  funext x y; apply propext; constructor
  · intro h; exact congrFun (hr y (Or.inl ⟨x,h⟩)) x ▸ h
  · intro h; exact congrFun (hl x (Or.inr ⟨y,h⟩)).symm y ▸ h
/-- PM I ✱71·36. -/
theorem star_71_36 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (x y : α) (hy : cod R y) : x = f y ↔ R x y := by
  constructor
  · rintro rfl; exact hf y hy
  · intro hx; exact hR hx (hf y hy)
/-- PM I ✱71·361. -/
theorem star_71_361 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (x y : α) (hx : dom R x) : y = f x ↔ R x y := by
  constructor
  · rintro rfl; exact hf x hx
  · intro hy; exact hR hy (hf x hx)
/-- PM I ✱71·362. -/
theorem star_71_362 (R : Rel α) (f g : α → α) (hR : OneOne R)
    (hf : ∀ y, cod R y → R (f y) y) (hg : ∀ x, dom R x → R x (g x))
    (x y : α) (hx : dom R x) (hy : cod R y) : (x = f y ↔ R x y) ∧ (R x y ↔ y = g x) :=
  ⟨star_71_36 R f hR.1 hf x y hy,(star_71_361 R g hR.2 hg x y hx).symm⟩
/-- PM I ✱71·37. -/
theorem star_71_37 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a : Class α) (y : α) (hy : cod R y) :
    converseImage R a y ↔ a (f y) := by
  constructor
  · rintro ⟨x,ha,hx⟩; simpa [hR hx (hf y hy)] using ha
  · intro ha; exact ⟨f y,ha,hf y hy⟩

end PM.Architecture.Star71DescriptionKernel
