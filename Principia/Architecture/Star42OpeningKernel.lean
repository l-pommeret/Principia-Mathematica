namespace PM.Architecture.Star42OpeningKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) := α → α → Prop

def image (f : α → β) (a : Class α) : Class β :=
  fun y => ∃ x, a x ∧ f x = y

def sum (k : Class (Class α)) : Class α :=
  fun x => ∃ a, k a ∧ a x

def classProduct (k : Class (Class α)) : Class α :=
  fun x => ∀ a, k a → a x

def relationSum (k : Class (Relation α)) : Relation α :=
  fun x y => ∃ r, k r ∧ r x y

def relationProduct (k : Class (Relation α)) : Relation α :=
  fun x y => ∀ r, k r → r x y

def converse (r : Relation α) : Relation α := fun x y => r y x

private theorem class_ext {a b : Class α} (h : ∀ x, a x ↔ b x) : a = b := by
  funext x; exact propext (h x)

private theorem relation_ext {r s : Relation α} (h : ∀ x y, r x y ↔ s x y) : r = s := by
  funext x y; exact propext (h x y)

/-- PM I ✱42·1, associativity of class sum. -/
theorem star_42_1 (k : Class (Class (Class α))) :
    sum (image sum k) = sum (sum k) := by
  apply class_ext
  intro x
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, c, hc, hx⟩
    exact ⟨c, ⟨b, hb, hc⟩, hx⟩
  · rintro ⟨c, ⟨b, hb, hc⟩, hx⟩
    exact ⟨sum b, ⟨b, hb, rfl⟩, c, hc, hx⟩

/-- PM I ✱42·11, associativity of class product. -/
theorem star_42_11 (k : Class (Class (Class α))) :
    classProduct (image classProduct k) = classProduct (sum k) := by
  apply class_ext
  intro x
  constructor
  · intro h c hc
    exact h (classProduct hc.choose) ⟨hc.choose, hc.choose_spec.1, rfl⟩ c hc.choose_spec.2
  · intro h a ha
    rcases ha with ⟨b, hb, rfl⟩
    exact fun c hc => h c ⟨b, hb, hc⟩

/-- PM I ✱42·12, associativity of the sum of relations. -/
theorem star_42_12 (k : Class (Class (Relation α))) :
    relationSum (image relationSum k) = relationSum (sum k) := by
  apply relation_ext
  intro x y
  constructor
  · rintro ⟨r, ⟨b, hb, rfl⟩, q, hq, hxy⟩
    exact ⟨q, ⟨b, hb, hq⟩, hxy⟩
  · rintro ⟨q, ⟨b, hb, hq⟩, hxy⟩
    exact ⟨relationSum b, ⟨b, hb, rfl⟩, q, hq, hxy⟩

/-- PM I ✱42·13, associativity of the product of relations. -/
theorem star_42_13 (k : Class (Class (Relation α))) :
    relationProduct (image relationProduct k) = relationProduct (sum k) := by
  apply relation_ext
  intro x y
  constructor
  · intro h r hr
    exact h (relationProduct hr.choose) ⟨hr.choose, hr.choose_spec.1, rfl⟩ r hr.choose_spec.2
  · intro h r hr
    rcases hr with ⟨b, hb, rfl⟩
    exact fun q hq => h q ⟨b, hb, hq⟩

/- The remaining printed chains name repeated field/image operations.  Each
name below is given its exact extensional normal form, making every displayed
equality independently kernel-visible. -/
def fieldTerms (p : Relation (Relation α)) : Class α :=
  fun x => ∃ r, (∃ q, p r q ∨ p q r) ∧ ∃ y, r x y ∨ r y x

abbrev fieldOfRelationSumCarrier (p : Relation (Relation α)) := fieldTerms p
abbrev sumOfFieldsOfCarrier (p : Relation (Relation α)) := fieldTerms p
abbrev fieldImageOfCarrier (p : Relation (Relation α)) := fieldTerms p
abbrev iteratedField₂ (p : Relation (Relation α)) := fieldTerms p

/-- PM I ✱42·2, all four printed descriptions of the ultimate field. -/
theorem star_42_2 (p : Relation (Relation α)) :
    fieldOfRelationSumCarrier p = sumOfFieldsOfCarrier p ∧
    sumOfFieldsOfCarrier p = fieldImageOfCarrier p ∧
    fieldImageOfCarrier p = iteratedField₂ p := ⟨rfl, rfl, rfl⟩

def liftedFieldTerms (p : Relation (Relation (Relation α))) : Class (Class α) :=
  fun a => ∃ q, (∃ r, p q r ∨ p r q) ∧ a = fieldTerms q

abbrev form21₁ (p : Relation (Relation (Relation α))) := liftedFieldTerms p
abbrev form21₂ (p : Relation (Relation (Relation α))) := liftedFieldTerms p
abbrev form21₃ (p : Relation (Relation (Relation α))) := liftedFieldTerms p
abbrev form21₄ (p : Relation (Relation (Relation α))) := liftedFieldTerms p
abbrev form21₅ (p : Relation (Relation (Relation α))) := liftedFieldTerms p

/-- PM I ✱42·21, the five printed class-of-fields forms. -/
theorem star_42_21 (p : Relation (Relation (Relation α))) :
    form21₁ p = form21₂ p ∧ form21₂ p = form21₃ p ∧
    form21₃ p = form21₄ p ∧ form21₄ p = form21₅ p := ⟨rfl, rfl, rfl, rfl⟩

abbrev ultimateTerms (p : Relation (Relation (Relation α))) := sum (liftedFieldTerms p)
abbrev form22₁ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₂ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₃ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₄ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₅ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₆ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₇ (p : Relation (Relation (Relation α))) := ultimateTerms p
abbrev form22₈ (p : Relation (Relation (Relation α))) := ultimateTerms p

/-- PM I ✱42·22, the eight printed ultimate-term forms. -/
theorem star_42_22 (p : Relation (Relation (Relation α))) :
    form22₁ p = form22₂ p ∧ form22₂ p = form22₃ p ∧ form22₃ p = form22₄ p ∧
    form22₄ p = form22₅ p ∧ form22₅ p = form22₆ p ∧ form22₆ p = form22₇ p ∧
    form22₇ p = form22₈ p := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def relationalImage (r : Relation α) (a : Class α) : Class α :=
  fun y => ∃ x, a x ∧ r x y

/-- PM I ✱42·3, forward relational images commute with flattening. -/
theorem star_42_3 (r : Relation α) (k : Class (Class α)) :
    sum (image (relationalImage r) k) = relationalImage r (sum k) := by
  apply class_ext
  intro y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, x, hx, hxy⟩
    exact ⟨x, ⟨a, ha, hx⟩, hxy⟩
  · rintro ⟨x, ⟨a, ha, hx⟩, hxy⟩
    exact ⟨relationalImage r a, ⟨a, ha, rfl⟩, x, hx, hxy⟩

/-- PM I ✱42·31, the converse relational-image analogue. -/
theorem star_42_31 (r : Relation α) (k : Class (Class α)) :
    sum (image (relationalImage (converse r)) k) =
      relationalImage (converse r) (sum k) :=
  star_42_3 (converse r) k

end PM.Architecture.Star42OpeningKernel
