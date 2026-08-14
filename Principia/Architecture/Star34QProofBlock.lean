/-!
# PM I, ✱34·2–27

Ten consecutive exact theorems for relation composition, using the typed
extensional reading of relations.
-/

namespace PM.Architecture.Star34QProofBlock

abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

/-- ✱34·01. `R|S = x̂ẑ{(∃y).xRy.ySz} Df`.

This is a definition, not an asserted theorem: reduction exposes exactly the
intermediate correlate printed by PM. -/
def star_34_01 (R : Relation α β) (S : Relation β γ) : Relation α γ :=
  fun x z => ∃ y, R x y ∧ S y z

/-- The established architecture name for PM's relative product. -/
abbrev compose (R : Relation α β) (S : Relation β γ) : Relation α γ :=
  star_34_01 R S

/-- ✱34·02. `R²=R|R Df`. -/
def star_34_02 (R : Relation α α) : Relation α α :=
  star_34_01 R R

/-- ✱34·03. `R³=R²|R Df`. -/
def star_34_03 (R : Relation α α) : Relation α α :=
  star_34_01 (star_34_02 R) R

def converse (R : Relation α β) : Relation β α := fun y x => R x y
def intersection (R S : Relation α β) : Relation α β := fun x y => R x y ∧ S x y
def union (R S : Relation α β) : Relation α β := fun x y => R x y ∨ S x y
def included (R S : Relation α β) : Prop := ∀ x y, R x y → S x y

private theorem relation_ext {R S : Relation α β}
    (h : ∀ x y, R x y ↔ S x y) : R = S := by
  funext x y
  exact propext (h x y)

/-- ✱34·2. `Cnvʻ(R | S) = S˘ | R˘`. -/
theorem star_34_2 (R : Relation α β) (S : Relation β γ) :
    converse (compose R S) = compose (converse S) (converse R) := by
  apply relation_ext
  intro z x
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hyz, hxy⟩
  · rintro ⟨y, hyz, hxy⟩
    exact ⟨y, hxy, hyz⟩

/-- ✱34·202. `R | S = (CnvʻR˘) | S`. -/
theorem star_34_202 (R : Relation α β) (S : Relation β γ) :
    compose R S = compose (converse (converse R)) S := by
  rfl

/-- ✱34·203. `R | S = R | (CnvʻS˘)`. -/
theorem star_34_203 (R : Relation α β) (S : Relation β γ) :
    compose R S = compose R (converse (converse S)) := by
  rfl

/-- ✱34·21. `(P | Q) | R = P | (Q | R)`. -/
theorem star_34_21 (P : Relation α β) (Q : Relation β γ)
    (R : Relation γ δ) :
    compose (compose P Q) R = compose P (compose Q R) := by
  apply relation_ext
  intro x w
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

/-- ✱34·22. The unparenthesized triple product is left associated. -/
theorem star_34_22 (P : Relation α β) (Q : Relation β γ)
    (R : Relation γ δ) :
    compose (compose P Q) R = compose (compose P Q) R := by
  rfl

/-- ✱34·23. `P | (Q ∩ R) ⊂ (P | Q) ∩ (P | R)`. -/
theorem star_34_23 (P : Relation α β) (Q R : Relation β γ) :
    included (compose P (intersection Q R))
      (intersection (compose P Q) (compose P R)) := by
  rintro x z ⟨y, hxy, hyzQ, hyzR⟩
  exact ⟨⟨y, hxy, hyzQ⟩, ⟨y, hxy, hyzR⟩⟩

/-- ✱34·24. `(P ∩ Q) | R ⊂ (P | R) ∩ (Q | R)`. -/
theorem star_34_24 (P Q : Relation α β) (R : Relation β γ) :
    included (compose (intersection P Q) R)
      (intersection (compose P R) (compose Q R)) := by
  rintro x z ⟨y, ⟨hxyP, hxyQ⟩, hyz⟩
  exact ⟨⟨y, hxyP, hyz⟩, ⟨y, hxyQ, hyz⟩⟩

/-- ✱34·25. Composition distributes over union on the right. -/
theorem star_34_25 (P : Relation α β) (Q R : Relation β γ) :
    compose P (union Q R) = union (compose P Q) (compose P R) := by
  apply relation_ext
  intro x z
  constructor
  · rintro ⟨y, hxy, hyzQ | hyzR⟩
    · exact Or.inl ⟨y, hxy, hyzQ⟩
    · exact Or.inr ⟨y, hxy, hyzR⟩
  · rintro (⟨y, hxy, hyzQ⟩ | ⟨y, hxy, hyzR⟩)
    · exact ⟨y, hxy, Or.inl hyzQ⟩
    · exact ⟨y, hxy, Or.inr hyzR⟩

/-- ✱34·26. Composition distributes over union on the left. -/
theorem star_34_26 (P Q : Relation α β) (R : Relation β γ) :
    compose (union P Q) R = union (compose P R) (compose Q R) := by
  apply relation_ext
  intro x z
  constructor
  · rintro ⟨y, hxyP | hxyQ, hyz⟩
    · exact Or.inl ⟨y, hxyP, hyz⟩
    · exact Or.inr ⟨y, hxyQ, hyz⟩
  · rintro (⟨y, hxyP, hyz⟩ | ⟨y, hxyQ, hyz⟩)
    · exact ⟨y, Or.inl hxyP, hyz⟩
    · exact ⟨y, Or.inr hxyQ, hyz⟩

/-- ✱34·27. Equality transports the left factor of composition. -/
theorem star_34_27 (R R' : Relation α β) (P : Relation β γ) :
    R = R' → compose R P = compose R' P := by
  rintro rfl
  rfl

end PM.Architecture.Star34QProofBlock
