import Principia.FirstEdition.Volume1.Star40Source

namespace PM.Architecture.Star40OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev ClassFamily (α : Type u) := Class α → Prop

def Included (a b : Class α) : Prop := ∀ x, a x → b x

/-- ✱40·01: the product of a class of classes. -/
def Product (κ : ClassFamily α) : Class α :=
  fun x => ∀ a, κ a → a x

/-- ✱40·02: the sum of a class of classes. -/
def Sum (κ : ClassFamily α) : Class α :=
  fun x => ∃ a, κ a ∧ a x

theorem star_40_01 (κ : ClassFamily α) :
    Product κ = fun x => ∀ a, κ a → a x := by
  rfl

theorem star_40_02 (κ : ClassFamily α) :
    Sum κ = fun x => ∃ a, κ a ∧ a x := by
  rfl

theorem star_40_1 (κ : ClassFamily α) (x : α) :
    Product κ x ↔ ∀ a, κ a → a x := by
  rfl

theorem star_40_11 (κ : ClassFamily α) (x : α) :
    Sum κ x ↔ ∃ a, κ a ∧ a x := by
  rfl

theorem star_40_12 (κ : ClassFamily α) (a : Class α) :
    κ a → Included (Product κ) a := by
  intro ha x hx
  exact hx a ha

theorem star_40_13 (κ : ClassFamily α) (a : Class α) :
    κ a → Included a (Sum κ) := by
  intro ha x hx
  exact ⟨a, ha, hx⟩

theorem star_40_14 (κ : ClassFamily α) (a : Class α) (x : α) :
    κ a → Product κ x → a x := by
  intro ha hx
  exact hx a ha

theorem star_40_141 (κ : ClassFamily α) (a : Class α) (x : α) :
    κ a → a x → Sum κ x := by
  intro ha hx
  exact ⟨a, ha, hx⟩

theorem star_40_15 (κ : ClassFamily α) (b : Class α) :
    Included b (Product κ) ↔ ∀ c, κ c → Included b c := by
  constructor
  · intro h c hc x hx
    exact h x hx c hc
  · intro h x hx c hc
    exact h c hc x hx

theorem star_40_151 (κ : ClassFamily α) (b : Class α) :
    Included (Sum κ) b ↔ ∀ c, κ c → Included c b := by
  constructor
  · intro h c hc x hx
    exact h x ⟨c, hc, hx⟩
  · rintro h x ⟨c, hc, hx⟩
    exact h c hc x hx

end PM.Architecture.Star40OpeningKernel
