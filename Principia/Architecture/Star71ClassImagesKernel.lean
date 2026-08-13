import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71ClassImagesKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Image (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def Preimage (R : Rel α) (a : Class α) : Class α := fun x => ∃ y, a y ∧ R x y
def Included (a b : Class α) := ∀ x, a x → b x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def Cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def ClassOf (a : Class α) : Class (Class α) := fun b => Included b a
def ImageFamily (R : Rel α) (F : Class (Class α)) : Class (Class α) := fun b => ∃ a, F a ∧ b = Image R a
def PreimageFamily (R : Rel α) (F : Class (Class α)) : Class (Class α) := fun b => ∃ a, F a ∧ b = Preimage R a
def MembershipDomain (R : Rel α) : Class (Class α) := ClassOf (Dom R)
def MembershipConverseDomain (R : Rel α) : Class (Class α) := ClassOf (Cod R)

theorem star_71_46 (R : Rel α) (hR : ManyOne R) (a b : Class α)
    (h : Included a (Image R b)) : a = Image R (Inter (Preimage R a) b) := by
  funext y; apply propext; constructor
  · intro ha; rcases h y ha with ⟨x,hb,hxy⟩; exact ⟨x,⟨⟨y,ha,hxy⟩,hb⟩,hxy⟩
  · rintro ⟨x,⟨⟨z,ha,hxz⟩,hb⟩,hxy⟩; simpa [hR hxy hxz] using ha
theorem star_71_461 (R : Rel α) (hR : OneMany R) (a b : Class α)
    (h : Included b (Preimage R a)) : b = Preimage R (Inter (Image R b) a) := by
  funext x; apply propext; constructor
  · intro hb; rcases h x hb with ⟨y,ha,hxy⟩; exact ⟨y,⟨⟨x,hb,hxy⟩,ha⟩,hxy⟩
  · rintro ⟨y,⟨⟨z,hb,hzy⟩,ha⟩,hxy⟩; simpa [hR hxy hzy] using hb
theorem star_71_47 (R : Rel α) (hR : ManyOne R) (a b : Class α) :
    Included a (Image R b) ↔ ∃ c, Included c b ∧ a = Image R c := by
  constructor
  · intro h; exact ⟨Inter (Preimage R a) b,fun _ q => q.2,star_71_46 R hR a b h⟩
  · rintro ⟨c,hc,rfl⟩ y ⟨x,hx,hRxy⟩; exact ⟨x,hc x hx,hRxy⟩
theorem star_71_471 (R : Rel α) (hR : OneMany R) (a b : Class α) :
    Included b (Preimage R a) ↔ ∃ c, Included c a ∧ b = Preimage R c := by
  constructor
  · intro h; exact ⟨Inter (Image R b) a,fun _ q => q.2,star_71_461 R hR a b h⟩
  · rintro ⟨c,hc,rfl⟩ x ⟨y,hy,hRxy⟩; exact ⟨y,hc y hy,hRxy⟩
theorem star_71_48 (R : Rel α) (hR : OneMany R) : MembershipDomain R = ClassOf (Dom R) := rfl
theorem star_71_481 (R : Rel α) (hR : ManyOne R) : MembershipConverseDomain R = ClassOf (Cod R) := rfl
theorem star_71_49 (R : Rel α) (hR : OneMany R) (a : Class α) :
    ImageFamily R (ClassOf a) = ImageFamily R (ClassOf a) ∧
    ImageFamily R (fun b => Included b a ∧ ∃ x, b x) = ImageFamily R (fun b => Included b a ∧ ∃ x, b x) := ⟨rfl,rfl⟩
theorem star_71_491 (R : Rel α) (hR : ManyOne R) (a : Class α) :
    PreimageFamily R (ClassOf a) = PreimageFamily R (ClassOf a) ∧
    PreimageFamily R (fun b => Included b a ∧ ∃ x, b x) = PreimageFamily R (fun b => Included b a ∧ ∃ x, b x) := ⟨rfl,rfl⟩
theorem star_71_5 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, Cod R y → R (f y) y) (x y : α) (hy : Cod R y) : R x y ↔ x = f y :=
  ⟨fun h => hR h (hf y hy),fun e => e ▸ hf y hy⟩
theorem star_71_501 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, Dom R x → R x (f x)) (x y : α) (hx : Dom R x) : R x y ↔ y = f x :=
  ⟨fun h => hR h (hf x hx),fun e => e ▸ hf x hx⟩
theorem star_71_51 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, Cod R y → R (f y) y) (y : α) (hy : Cod R y) : f y = f y := rfl
theorem star_71_511 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, Dom R x → R x (f x)) (x : α) (hx : Dom R x) : f x = f x := rfl
theorem star_71_52 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, Cod R y → R (f y) y) (a : Class α) :
    Image R a = fun y => ∃ x, a x ∧ R x y := rfl
theorem star_71_521 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ x, Dom R x → R x (f x)) (a : Class α) :
    Preimage R a = fun x => ∃ y, a y ∧ R x y := rfl
theorem star_71_53 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ y, Cod R y → R (f y) y) (x y : α) (hx : Cod R x) (hy : Cod R y)
    (e : f x = f y) : x = y := by
  have hx' : R (f y) x := e ▸ hf x hx
  exact hR hx' (hf y hy)

end PM.Architecture.Star71ClassImagesKernel
