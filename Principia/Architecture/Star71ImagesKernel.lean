import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71ImagesKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def image (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def converseImage (R : Rel α) (a : Class α) : Class α := fun x => ∃ y, a y ∧ R x y
def diff (a b : Class α) : Class α := fun x => a x ∧ ¬ b x
def included (a b : Class α) := ∀ x, a x → b x

/-- PM I ✱71·371. -/
theorem star_71_371 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ x, cod R x → R (f x) x) (a : Class α) (x : α) (hx : cod R x) :
    image R a x ↔ a (f x) := by
  constructor
  · rintro ⟨y,ha,hy⟩; simpa [hR hy (hf x hx)] using ha
  · intro ha; exact ⟨f x,ha,hf x hx⟩
/-- PM I ✱71·38. -/
theorem star_71_38 (R : Rel α) (hR : ManyOne R) (a b : Class α) :
    converseImage R (diff a b) = diff (converseImage R a) (converseImage R b) := by
  funext y; apply propext; constructor
  · rintro ⟨x,⟨ha,hnb⟩,hx⟩; exact ⟨⟨x,ha,hx⟩,fun ⟨z,hb,hz⟩ => hnb (hR hz hx ▸ hb)⟩
  · rintro ⟨⟨x,ha,hx⟩,hnot⟩; exact ⟨x,⟨ha,fun hb => hnot ⟨x,hb,hx⟩⟩,hx⟩
/-- PM I ✱71·381. -/
theorem star_71_381 (R : Rel α) (hR : OneMany R) (a b : Class α) :
    image R (diff a b) = diff (image R a) (image R b) := by
  funext x; apply propext; constructor
  · rintro ⟨y,⟨ha,hnb⟩,hy⟩; exact ⟨⟨y,ha,hy⟩,fun ⟨z,hb,hz⟩ => hnb (hR hz hy ▸ hb)⟩
  · rintro ⟨⟨y,ha,hy⟩,hnot⟩; exact ⟨y,⟨ha,fun hb => hnot ⟨y,hb,hy⟩⟩,hy⟩
/-- PM I ✱71·4. -/
theorem star_71_4 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a : Class α) (x : α) :
    converseImage R a x ↔ ∃ y, a y ∧ cod R y ∧ x = f y := by
  constructor
  · rintro ⟨y,ha,hx⟩; exact ⟨y,ha,⟨x,hx⟩,hR hx (hf y ⟨x,hx⟩)⟩
  · rintro ⟨y,ha,hy,rfl⟩; exact ⟨y,ha,hf y hy⟩
/-- PM I ✱71·401. -/
theorem star_71_401 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a : Class α) (y : α) :
    image R a y ↔ ∃ x, a x ∧ dom R x ∧ y = f x := by
  constructor
  · rintro ⟨x,ha,hy⟩; exact ⟨x,ha,⟨y,hy⟩,hR hy (hf x ⟨y,hy⟩)⟩
  · rintro ⟨x,ha,hx,rfl⟩; exact ⟨x,ha,hf x hx⟩
/-- PM I ✱71·41. -/
theorem star_71_41 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (x : α) : dom R x ↔ ∃ y, cod R y ∧ x = f y := by
  constructor
  · rintro ⟨y,hx⟩; exact ⟨y,⟨x,hx⟩,hR hx (hf y ⟨x,hx⟩)⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨y,hf y hy⟩
/-- PM I ✱71·411. -/
theorem star_71_411 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (y : α) : cod R y ↔ ∃ x, dom R x ∧ y = f x := by
  constructor
  · rintro ⟨x,hy⟩; exact ⟨x,⟨y,hy⟩,hR hy (hf x ⟨y,hy⟩)⟩
  · rintro ⟨x,hx,rfl⟩; exact ⟨x,hf x hx⟩
/-- PM I ✱71·42. -/
theorem star_71_42 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a b : Class α) (hb : included b (cod R)) :
    included (converseImage R b) a ↔ ∀ y, b y → a (f y) := by
  constructor
  · intro h y hy; exact h _ ⟨y,hy,hf y (hb y hy)⟩
  · rintro h x ⟨y,hy,hx⟩; simpa [hR hx (hf y (hb y hy))] using h y hy
/-- PM I ✱71·421. -/
theorem star_71_421 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a b : Class α) (ha : included a (dom R)) :
    included (image R a) b ↔ ∀ x, a x → b (f x) := by
  constructor
  · intro h x hx; exact h _ ⟨x,hx,hf x (ha x hx)⟩
  · rintro h y ⟨x,hx,hy⟩; simpa [hR hy (hf x (ha x hx))] using h x hx
/-- PM I ✱71·43. -/
theorem star_71_43 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a : Class α) (y : α)
    (ha : a y) (hy : cod R y) : converseImage R a (f y) := ⟨y,ha,hf y hy⟩
/-- PM I ✱71·431. -/
theorem star_71_431 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a : Class α) (x : α)
    (ha : a x) (hx : dom R x) : image R a (f x) := ⟨x,ha,hf x hx⟩
/-- PM I ✱71·44. -/
theorem star_71_44 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a : Class α) (ha : included a (cod R)) (ψ : Class α) :
    (∀ x, converseImage R a x → ψ x) ↔ ∀ y, a y → ψ (f y) := by
  constructor
  · intro h y hy; exact h _ ⟨y,hy,hf y (ha y hy)⟩
  · rintro h x ⟨y,hy,hx⟩; simpa [hR hx (hf y (ha y hy))] using h y hy
/-- PM I ✱71·441. -/
theorem star_71_441 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a : Class α) (ha : included a (dom R)) (ψ : Class α) :
    (∀ y, image R a y → ψ y) ↔ ∀ x, a x → ψ (f x) := by
  constructor
  · intro h x hx; exact h _ ⟨x,hx,hf x (ha x hx)⟩
  · rintro h y ⟨x,hx,hy⟩; simpa [hR hy (hf x (ha x hx))] using h x hx
/-- PM I ✱71·45. -/
theorem star_71_45 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, cod R y → R (f y) y) (a ψ : Class α) :
    (∃ x, converseImage R a x ∧ ψ x) ↔ ∃ y, a y ∧ cod R y ∧ ψ (f y) := by
  constructor
  · rintro ⟨x,⟨y,ha,hx⟩,hp⟩; exact ⟨y,ha,⟨x,hx⟩,by simpa [hR hx (hf y ⟨x,hx⟩)] using hp⟩
  · rintro ⟨y,ha,hy,hp⟩; exact ⟨f y,⟨y,ha,hf y hy⟩,hp⟩
/-- PM I ✱71·451. -/
theorem star_71_451 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, dom R x → R x (f x)) (a ψ : Class α) :
    (∃ y, image R a y ∧ ψ y) ↔ ∃ x, a x ∧ dom R x ∧ ψ (f x) := by
  constructor
  · rintro ⟨y,⟨x,ha,hy⟩,hp⟩; exact ⟨x,ha,⟨y,hy⟩,by simpa [hR hy (hf x ⟨y,hy⟩)] using hp⟩
  · rintro ⟨x,ha,hx,hp⟩; exact ⟨f x,⟨x,ha,hf x hx⟩,hp⟩

end PM.Architecture.Star71ImagesKernel
