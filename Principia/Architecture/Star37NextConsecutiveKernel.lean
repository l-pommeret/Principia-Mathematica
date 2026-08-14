namespace PM.Architecture.Star37NextConsecutiveKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def Included (A B : Class α) : Prop := ∀ x, A x → B x
def inter (A B : Class α) : Class α := fun x => A x ∧ B x
def universalClass (α : Sort u) : Class α := fun _ => True
def nonemptyClass (A : Class α) : Prop := ∃ x, A x

def converse (R : Relation α β) : Relation β α := fun y x => R x y
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def converseDomain (R : Relation α β) : Class β := fun y => ∃ x, R x y
def image (R : Relation α β) (B : Class β) : Class α :=
  fun x => ∃ y, B y ∧ R x y

/-- PM I ✱37·01: relational image, as an eliminable definition. -/
def star_37_01 (R : Relation α β) (B : Class β) : Class α :=
  fun x => ∃ y, B y ∧ R x y

/-- The relation `R_∈` of ✱37·101: an output class is related to an input
class exactly when it is the image of that input class. -/
def imageRelation (R : Relation α β) : Relation (Class α) (Class β) :=
  fun A B => A = image R B

/-- PM I ✱37·02: the relation whose value at `B` is the image `R``B`. -/
def star_37_02 (R : Relation α β) : Relation (Class α) (Class β) :=
  fun A B => A = star_37_01 R B

/-- PM I ✱37·03: converse of the image relation. -/
def star_37_03 (R : Relation α β) : Relation (Class β) (Class α) :=
  converse (star_37_02 R)

/-- PM I ✱37·04: the image, under `R_∈`, of a class of classes. -/
def star_37_04 (R : Relation α β) (K : Class (Class β)) : Class (Class α) :=
  image (star_37_02 R) K

/-- PM I ✱37·05: every member of `B` has a unique `R`-value. -/
def star_37_05 (R : Relation α β) (B : Class β) : Prop :=
  ∀ y, B y → ∃ x, R x y ∧ ∀ z, R z y → z = x

/-- PM I ✱37·23. -/
theorem star_37_23 (R : Relation α β) :
    domain (imageRelation R) =
      (fun A => ∃ B, A = image R B) := by
  rfl

/-- PM I ✱37·231. -/
theorem star_37_231 (R : Relation α β) :
    converseDomain (imageRelation R) = universalClass (Class β) := by
  funext B
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    exact ⟨image R B, rfl⟩

/-- PM I ✱37·24. -/
theorem star_37_24 (R : Relation α β) (A : Class α) :
    domain (imageRelation R) A → Included A (domain R) := by
  rintro ⟨B, rfl⟩ x ⟨y, _, related⟩
  exact ⟨y, related⟩

/-- First conjunct of the paired theorem PM I ✱37·25. -/
theorem star_37_25_domain (R : Relation α β) :
    domain R = image R (converseDomain R) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, related⟩
    exact ⟨y, ⟨x, related⟩, related⟩
  · rintro ⟨y, _, related⟩
    exact ⟨y, related⟩

/-- Second conjunct of the paired theorem PM I ✱37·25. -/
theorem star_37_25_converseDomain (R : Relation α β) :
    converseDomain R = image (converse R) (domain R) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, related⟩
    exact ⟨x, ⟨y, related⟩, related⟩
  · rintro ⟨x, _, related⟩
    exact ⟨x, related⟩

/-- Exact paired theorem PM I ✱37·25. -/
theorem star_37_25 (R : Relation α β) :
    domain R = image R (converseDomain R) ∧
      converseDomain R = image (converse R) (domain R) :=
  ⟨star_37_25_domain R, star_37_25_converseDomain R⟩

/-- PM I ✱37·26. -/
theorem star_37_26 (R : Relation α β) (B : Class β) :
    image R B = image R (inter B (converseDomain R)) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, member, related⟩
    exact ⟨y, ⟨member, ⟨x, related⟩⟩, related⟩
  · rintro ⟨y, ⟨member, _⟩, related⟩
    exact ⟨y, member, related⟩

/-- PM I ✱37·261. -/
theorem star_37_261 (R : Relation α β) (A : Class α) :
    image (converse R) A = image (converse R) (inter A (domain R)) := by
  funext y
  apply propext
  constructor
  · rintro ⟨x, member, related⟩
    exact ⟨x, ⟨member, ⟨y, related⟩⟩, related⟩
  · rintro ⟨x, ⟨member, _⟩, related⟩
    exact ⟨x, member, related⟩

/-- PM I ✱37·262. -/
theorem star_37_262 (R : Relation α β) (A B : Class β) :
    inter A (converseDomain R) = inter B (converseDomain R) →
      image R A = image R B := by
  intro restrictedEquality
  rw [star_37_26 R A, star_37_26 R B, restrictedEquality]

/-- PM I ✱37·263. -/
theorem star_37_263 (R : Relation α β) (A B : Class α) :
    inter A (domain R) = inter B (domain R) →
      image (converse R) A = image (converse R) B := by
  intro restrictedEquality
  rw [star_37_261 R A, star_37_261 R B, restrictedEquality]

/-- PM I ✱37·264.  PM's `∃!A` notation here means that the class `A` is
inhabited, as defined at ✱24·03; it is not unique existence. -/
theorem star_37_264 (R : Relation α β) (A : Class α) (B : Class β) :
    (nonemptyClass (inter A (image R B)) ↔
      (∃ x y, A x ∧ B y ∧ R x y)) ∧
    ((∃ x y, A x ∧ B y ∧ R x y) ↔
      nonemptyClass (inter B (image (converse R) A))) := by
  constructor
  · constructor
    · rintro ⟨x, memberA, y, memberB, related⟩
      exact ⟨x, y, memberA, memberB, related⟩
    · rintro ⟨x, y, memberA, memberB, related⟩
      exact ⟨x, memberA, ⟨y, memberB, related⟩⟩
  · constructor
    · rintro ⟨x, y, memberA, memberB, related⟩
      exact ⟨y, memberB, ⟨x, memberA, related⟩⟩
    · rintro ⟨y, memberB, x, memberA, related⟩
      exact ⟨x, y, memberA, memberB, related⟩

end PM.Architecture.Star37NextConsecutiveKernel
