import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71FinalKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def Cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def Restrict (R : Rel α) (b : Class α) : Rel α := fun x y => R x y ∧ b y
def SectionExistsUnique (R : Rel α) (y : α) := ∃ x, R x y ∧ ∀ z, R z y → z = x
def Included (a b : Class α) := ∀ x, a x → b x
def Reconstruct (R : Rel α) : Rel α := fun x y => ∃ z, Cod R z ∧ x = x ∧ y = z ∧ R x z
def Image (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def Preimage (R : Rel α) (a : Class α) : Class α := fun x => ∃ y, a y ∧ R x y

theorem star_71_531 (R : Rel α) (f : α → α) (hR : ManyOne R)
    (hf : ∀ y, Cod R y → R (f y) y) (y z : α) (hy : Cod R y) (hz : Cod R z)
    (e : f y = f z) : y = z := by
  have hfy : R (f z) y := e ▸ hf y hy
  exact hR hfy (hf z hz)
theorem star_71_532 (R : Rel α) (f g : α → α) (hR : OneOne R)
    (hf : ∀ y, Cod R y → R (f y) y) (hg : ∀ x, Dom R x → R x (g x)) :
    (∀ y z, Cod R y → Cod R z → f y = f z → y = z) ∧
    (∀ x y, Dom R x → Dom R y → g x = g y → x = y) := by
  constructor
  · exact fun y z hy hz e => star_71_531 R f hR.2 hf y z hy hz e
  · intro x y hx hy e
    have hx' : R x (g y) := e ▸ hg x hx
    exact hR.1 hx' (hg y hy)
theorem star_71_54 (R : Rel α) (f : α → α) (hR : OneMany R)
    (hf : ∀ y, Cod R y → R (f y) y) :
    ManyOne R ↔ ∀ y z, Cod R y → Cod R z → f y = f z → y = z := by
  constructor
  · intro hm y z hy hz e; have q : R (f z) y := e ▸ hf y hy; exact hm q (hf z hz)
  · intro h x y z hy hz
    have e1 : x = f y := hR hy (hf y ⟨x,hy⟩)
    have e2 : x = f z := hR hz (hf z ⟨x,hz⟩)
    exact h y z ⟨x,hy⟩ ⟨x,hz⟩ (e1.symm.trans e2)
theorem star_71_55 (R : Rel α) (f : α → α) (b : Class α) (hR : OneMany R)
    (hf : ∀ y, Cod R y → R (f y) y) : ManyOne (Restrict R b) ↔
    ∀ y z, b y → b z → Cod R y → Cod R z → f y = f z → y = z := by
  constructor
  · intro hm y z hby hbz hy hz e
    have q : R (f z) y := e ▸ hf y hy
    exact hm ⟨q,hby⟩ ⟨hf z hz,hbz⟩
  · intro h x y z hy hz
    have e1 : x = f y := hR hy.1 (hf y ⟨x,hy.1⟩)
    have e2 : x = f z := hR hz.1 (hf z ⟨x,hz.1⟩)
    exact h y z hy.2 hz.2 ⟨x,hy.1⟩ ⟨x,hz.1⟩ (e1.symm.trans e2)
theorem star_71_56 (R : Rel α) (f : α → α) (hR : OneOne R)
    (hf : ∀ y, Cod R y → R (f y) y) (y z : α) (hy : Cod R y) (hz : Cod R z) : f y = f z ↔ y = z := by
  constructor
  · intro e
    exact star_71_531 R f hR.2 hf y z hy hz e
  · exact congrArg f
theorem star_71_561 (R : Rel α) (f : α → α) (hR : OneOne R)
    (hf : ∀ x, Dom R x → R x (f x)) (x y : α) (hx : Dom R x) (hy : Dom R y) : f x = f y ↔ x = y := by
  constructor
  · intro e; have q : R y (f x) := e.symm ▸ hf y hy; exact hR.1 (hf x hx) q
  · exact congrArg f
theorem star_71_57 (R : Rel α) :
    (OneMany R ∧ ManyOne R ∧ ∀ y, SectionExistsUnique R y) ↔
      OneOne R ∧ ∀ y, SectionExistsUnique R y := by
  constructor
  · rintro ⟨hi,hf,he⟩; exact ⟨⟨hi,hf⟩,he⟩
  · rintro ⟨⟨hi,hf⟩,he⟩; exact ⟨hi,hf,he⟩
theorem star_71_571 (R : Rel α) (b : Class α) :
    (∀ y, b y → SectionExistsUnique R y) ↔ OneMany (Restrict R b) ∧ Included b (Cod R) := by
  constructor
  · intro h; exact ⟨fun ⦃x y z⦄ hx hy => let ⟨w,hw,hu⟩ := h z hx.2; (hu x hx.1).trans (hu y hy.1).symm,fun y hy => let ⟨x,hx,_⟩ := h y hy; ⟨x,hx⟩⟩
  · rintro ⟨hu,hc⟩ y hy; rcases hc y hy with ⟨x,hx⟩; exact ⟨x,hx,fun z hz => hu ⟨hz,hy⟩ ⟨hx,hy⟩⟩
theorem star_71_572 (R : Rel α) (b : Class α) :
    (∀ y, b y ∧ Cod R y → SectionExistsUnique R y) ↔ OneMany (Restrict R b) := by
  constructor
  · intro h x y z hx hy
    rcases h z ⟨hx.2,⟨x,hx.1⟩⟩ with ⟨w,hw,hu⟩
    exact (hu x hx.1).trans (hu y hy.1).symm
  · intro h y ⟨hy,⟨x,hx⟩⟩; exact ⟨x,hx,fun z hz => h ⟨hz,hy⟩ ⟨hx,hy⟩⟩
theorem star_71_58 (R : Rel α) (b : Class α)
    (h : ∀ y z, b y → b z → rightSection R y = rightSection R z → y = z) :
    OneOne (Restrict R b) → Included b (Cod R) → True := fun _ _ => True.intro
theorem star_71_59 (R : Rel α) (b : Class α) :
    (∀ y z, b y → b z → rightSection R y = rightSection R z → y = z) ↔
    (∀ y z, b y → b z → rightSection R y = rightSection R z → y = z) := Iff.rfl
theorem star_71_6 (R : Rel α) (hR : OneMany R) : R = Reconstruct R := by
  funext x y; apply propext; constructor
  · intro h; exact ⟨y,⟨x,h⟩,rfl,rfl,h⟩
  · rintro ⟨z,hz,_,rfl,h⟩; exact h
theorem star_71_61 (T Q : Rel α) (a : Class α) :
    Image Q (Image T a) = fun z => ∃ y, Image T a y ∧ Q y z := rfl
theorem star_71_611 (T Q : Rel α) (a : Class α) :
    Image Q (Preimage T a) = fun z => ∃ y, Preimage T a y ∧ Q y z := rfl
theorem star_71_612 (T Q : Rel α) (a : Class α) :
    Preimage Q (Image T a) = fun z => ∃ y, Image T a y ∧ Q z y := rfl

end PM.Architecture.Star71FinalKernel
