import Principia.Architecture.Star40SecondKernel

namespace PM.Architecture.Star40ThirdKernel

open PM.Architecture.Star40OpeningKernel
open PM.Architecture.Star40SecondKernel

def FamilyExists (κ : ClassFamily α) : Prop := ∃ a, κ a
def ClassExists (a : Class α) : Prop := ∃ x, a x

theorem star_40_221 (κ : ClassFamily α) :
    κ Universal → Sum κ = Universal := by
  intro hV
  funext x
  apply propext
  constructor
  · intro _
    rfl
  · intro _
    exact ⟨Universal, hV, rfl⟩

theorem star_40_23 (κ : ClassFamily α) :
    FamilyExists κ → Included (Product κ) (Sum κ) := by
  rintro ⟨a, ha⟩ x hx
  exact ⟨a, ha, hx a ha⟩

theorem star_40_24 (κ : ClassFamily α) (b : Class α) :
    FamilyExists κ → (∀ c, κ c → Included b c) → Included b (Sum κ) := by
  rintro ⟨a, ha⟩ lower x hx
  exact ⟨a, ha, lower a ha x hx⟩

theorem star_40_25 (κ : ClassFamily α) (x : α) :
    Sum κ x ↔ FamilyExists (fun a => κ a ∧ a x) := by
  rfl

theorem star_40_26 (κ : ClassFamily α) :
    ClassExists (Sum κ) ↔ ∃ a, κ a ∧ ClassExists a := by
  constructor
  · rintro ⟨x, a, ha, hx⟩
    exact ⟨a, ha, x, hx⟩
  · rintro ⟨a, ha, x, hx⟩
    exact ⟨x, a, ha, hx⟩

theorem star_40_27 (κ : ClassFamily α) (a : Class α) :
    ClassInter a (Sum κ) = ClassEmpty ↔
      ∀ c, κ c → ClassInter a c = ClassEmpty := by
  constructor
  · intro h c hc
    funext x
    apply propext
    constructor
    · rintro ⟨ha, hcx⟩
      have hs : Sum κ x := ⟨c, hc, hcx⟩
      have : ClassInter a (Sum κ) x := ⟨ha, hs⟩
      rw [h] at this
      exact this
    · exact False.elim
  · intro h
    funext x
    apply propext
    constructor
    · rintro ⟨ha, c, hc, hcx⟩
      have : ClassInter a c x := ⟨ha, hcx⟩
      rw [h c hc] at this
      exact this
    · exact False.elim

def RelImage (R : Class α → Class α → Prop)
    (κ : ClassFamily α) : ClassFamily α :=
  fun output => ∃ input, κ input ∧ R input output

theorem star_40_3 (R : Class α → Class α → Prop) (κ familyL : ClassFamily α) :
    Product (RelImage R (FamilyUnion κ familyL)) =
      ClassInter (Product (RelImage R κ)) (Product (RelImage R familyL)) := by
  have imageUnion : RelImage R (FamilyUnion κ familyL) =
      FamilyUnion (RelImage R κ) (RelImage R familyL) := by
    funext output
    apply propext
    constructor
    · rintro ⟨input, hi | hi, hR⟩
      · exact Or.inl ⟨input, hi, hR⟩
      · exact Or.inr ⟨input, hi, hR⟩
    · rintro (⟨input, hi, hR⟩ | ⟨input, hi, hR⟩)
      · exact ⟨input, Or.inl hi, hR⟩
      · exact ⟨input, Or.inr hi, hR⟩
  rw [imageUnion, star_40_18]

theorem star_40_31 (R : Class α → Class α → Prop) (κ familyL : ClassFamily α) :
    Sum (RelImage R (FamilyUnion κ familyL)) =
      ClassUnion (Sum (RelImage R κ)) (Sum (RelImage R familyL)) := by
  have imageUnion : RelImage R (FamilyUnion κ familyL) =
      FamilyUnion (RelImage R κ) (RelImage R familyL) := by
    funext output
    apply propext
    constructor
    · rintro ⟨input, hi | hi, hR⟩
      · exact Or.inl ⟨input, hi, hR⟩
      · exact Or.inr ⟨input, hi, hR⟩
    · rintro (⟨input, hi, hR⟩ | ⟨input, hi, hR⟩)
      · exact ⟨input, Or.inl hi, hR⟩
      · exact ⟨input, Or.inr hi, hR⟩
  rw [imageUnion, star_40_171]

theorem star_40_32 (R : Class α → Class α → Prop) (κ familyL : ClassFamily α) :
    Included
      (ClassUnion (Product (RelImage R κ)) (Product (RelImage R familyL)))
      (Product (RelImage R (FamilyInter κ familyL))) := by
  rintro output (hκ | hL) result ⟨input, ⟨hiκ, hiL⟩, hR⟩
  · exact hκ result ⟨input, hiκ, hR⟩
  · exact hL result ⟨input, hiL, hR⟩

theorem star_40_33 (R : Class α → Class α → Prop) (κ familyL : ClassFamily α) :
    Included (Sum (RelImage R (FamilyInter κ familyL)))
      (ClassInter (Sum (RelImage R κ)) (Sum (RelImage R familyL))) := by
  rintro x ⟨output, ⟨input, ⟨hiκ, hiL⟩, hR⟩, hx⟩
  exact ⟨⟨output, ⟨input, hiκ, hR⟩, hx⟩,
    ⟨output, ⟨input, hiL, hR⟩, hx⟩⟩

end PM.Architecture.Star40ThirdKernel
