import Principia.Architecture.Star40OpeningKernel

namespace PM.Architecture.Star40SecondKernel

open PM.Architecture.Star40OpeningKernel

def FamilyIncluded (κ familyL : ClassFamily α) : Prop := ∀ a, κ a → familyL a
def FamilyInter (κ familyL : ClassFamily α) : ClassFamily α := fun a => κ a ∧ familyL a
def FamilyUnion (κ familyL : ClassFamily α) : ClassFamily α := fun a => κ a ∨ familyL a
def FamilyEmpty : ClassFamily α := fun _ => False
def ClassInter (a b : Class α) : Class α := fun x => a x ∧ b x
def ClassUnion (a b : Class α) : Class α := fun x => a x ∨ b x
def ClassEmpty : Class α := fun _ => False
def Universal : Class α := fun x => x = x

theorem star_40_16 (κ familyL : ClassFamily α) :
    FamilyIncluded κ familyL → Included (Product familyL) (Product κ) := by
  intro h x hx a ha
  exact hx a (h a ha)

theorem star_40_161 (κ familyL : ClassFamily α) :
    FamilyIncluded κ familyL → Included (Sum κ) (Sum familyL) := by
  rintro h x ⟨a, ha, hx⟩
  exact ⟨a, h a ha, hx⟩

theorem star_40_17 (κ familyL : ClassFamily α) :
    Included (ClassUnion (Product κ) (Product familyL))
      (Product (FamilyInter κ familyL)) := by
  rintro x (hx | hx) a ⟨haκ, haL⟩
  · exact hx a haκ
  · exact hx a haL

theorem star_40_171 (κ familyL : ClassFamily α) :
    ClassUnion (Sum κ) (Sum familyL) = Sum (FamilyUnion κ familyL) := by
  funext x
  apply propext
  constructor
  · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
    · exact ⟨a, Or.inl ha, hx⟩
    · exact ⟨a, Or.inr ha, hx⟩
  · rintro ⟨a, ha | ha, hx⟩
    · exact Or.inl ⟨a, ha, hx⟩
    · exact Or.inr ⟨a, ha, hx⟩

theorem star_40_18 (κ familyL : ClassFamily α) :
    Product (FamilyUnion κ familyL) = ClassInter (Product κ) (Product familyL) := by
  funext x
  apply propext
  constructor
  · intro hx
    exact ⟨fun a ha => hx a (Or.inl ha), fun a ha => hx a (Or.inr ha)⟩
  · rintro ⟨hκ, hL⟩ a (ha | ha)
    · exact hκ a ha
    · exact hL a ha

theorem star_40_181 (κ familyL : ClassFamily α) :
    Included (Sum (FamilyInter κ familyL)) (ClassInter (Sum κ) (Sum familyL)) := by
  rintro x ⟨a, ⟨haκ, haL⟩, hx⟩
  exact ⟨⟨a, haκ, hx⟩, ⟨a, haL, hx⟩⟩

theorem star_40_19 (κ : ClassFamily α) (x : α) :
    Sum κ x ↔ ∀ b, (∀ c, κ c → Included c b) → b x := by
  constructor
  · rintro ⟨a, ha, hx⟩ b upper
    exact upper a ha x hx
  · intro h
    exact h (Sum κ) (fun c hc => star_40_13 κ c hc)

theorem star_40_2 (κ : ClassFamily α) :
    κ = FamilyEmpty → Product κ = Universal := by
  intro hκ
  funext x
  apply propext
  constructor
  · intro _
    rfl
  · intro _ a ha
    rw [hκ] at ha
    exact ha.elim

theorem star_40_21 (κ : ClassFamily α) :
    κ = FamilyEmpty → Sum κ = ClassEmpty := by
  intro hκ
  funext x
  apply propext
  constructor
  · rintro ⟨a, ha, _⟩
    rw [hκ] at ha
    exact ha.elim
  · exact False.elim

theorem star_40_22 (κ : ClassFamily α) :
    κ ClassEmpty → Product κ = ClassEmpty := by
  intro hempty
  funext x
  apply propext
  constructor
  · intro hx
    exact hx ClassEmpty hempty
  · exact False.elim

end PM.Architecture.Star40SecondKernel
