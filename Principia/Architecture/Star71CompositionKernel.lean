import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71CompositionKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def Cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def Image (R : Rel α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ R x y
def Preimage (R : Rel α) (a : Class α) : Class α := fun x => ∃ y, a y ∧ R x y
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z

/-- PM I ✱71·613. -/
theorem star_71_613 (T Q : Rel α) (a : Class α) :
    Preimage Q (Preimage T a) = fun z => ∃ y, Preimage T a y ∧ Q z y := rfl

/-- PM I ✱71·7. -/
theorem star_71_7 (P Q : Rel α) (q : α → α) (hQ : OneMany Q)
    (hq : ∀ z, Cod Q z → Q (q z) z) (x z : α) (hz : Cod Q z) :
    comp P Q x z ↔ P x (q z) := by
  constructor
  · rintro ⟨y,hP,hQyz⟩
    simpa [hQ hQyz (hq z hz)] using hP
  · intro hP
    exact ⟨q z,hP,hq z hz⟩

/-- PM I ✱71·701. -/
theorem star_71_701 (Q P : Rel α) (q : α → α) (hQ : ManyOne Q)
    (hq : ∀ x, Dom Q x → Q x (q x)) (x z : α) (hx : Dom Q x) :
    comp Q P x z ↔ P (q x) z := by
  constructor
  · rintro ⟨y,hQxy,hP⟩
    simpa [hQ hQxy (hq x hx)] using hP
  · intro hP
    exact ⟨q x,hq x hx,hP⟩

end PM.Architecture.Star71CompositionKernel
