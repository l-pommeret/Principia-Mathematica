namespace PM.Architecture.Star35DomainUnionKernel

universe u v w

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def leftRestriction (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y

def rightRestriction (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y

def bothRestrictions (a : Class α) (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => a x ∧ R x y ∧ b y

def classIntersection (a b : Class α) : Class α := fun x => a x ∧ b x
def classUnion (a b : Class α) : Class α := fun x => a x ∨ b x
def relationUnion (R S : Relation α β) : Relation α β := fun x y => R x y ∨ S x y
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def converseDomain (R : Relation α β) : Class β := fun y => ∃ x, R x y

def composition (R : Relation α β) (S : Relation β γ) : Relation α γ :=
  fun x z => ∃ y, R x y ∧ S y z

/-- PM I ✱35·32. -/
theorem star_35_32 (a b : Class α) (R : Relation α β) :
    leftRestriction a (leftRestriction b R) =
      leftRestriction (classIntersection a b) R := by
  funext x y
  apply propext
  simp [leftRestriction, classIntersection, and_assoc]

/-- PM I ✱35·33. -/
theorem star_35_33 (a : Class α) (R : Relation α β) (b c : Class β) :
    rightRestriction (bothRestrictions a R b) c =
      bothRestrictions a R (classIntersection b c) := by
  funext x y
  apply propext
  simp [rightRestriction, bothRestrictions, classIntersection, and_assoc]

/-- PM I ✱35·34. -/
theorem star_35_34 (a b : Class α) (R : Relation α β) (c : Class β) :
    leftRestriction a (bothRestrictions b R c) =
      bothRestrictions (classIntersection a b) R c := by
  funext x y
  apply propext
  simp [leftRestriction, bothRestrictions, classIntersection, and_assoc]

/-- PM I ✱35·35. -/
theorem star_35_35 (a : Class α) (R : Relation α β) :
    leftRestriction a R = leftRestriction (classIntersection a (domain R)) R := by
  funext x y
  apply propext
  change (a x ∧ R x y) ↔ ((a x ∧ ∃ z, R x z) ∧ R x y)
  constructor
  · intro h
    exact ⟨⟨h.1, ⟨y, h.2⟩⟩, h.2⟩
  · intro h
    exact ⟨h.1.1, h.2⟩

/-- PM I ✱35·351. -/
theorem star_35_351 (R : Relation α β) (b : Class β) :
    rightRestriction R b =
      rightRestriction R (classIntersection b (converseDomain R)) := by
  funext x y
  apply propext
  change (R x y ∧ b y) ↔ (R x y ∧ b y ∧ ∃ z, R z y)
  constructor
  · intro h
    exact ⟨h.1, h.2, ⟨x, h.1⟩⟩
  · intro h
    exact ⟨h.1, h.2.1⟩

/-- PM I ✱35·352. -/
theorem star_35_352 (a : Class α) (R : Relation α β) (b : Class β) :
    bothRestrictions a R b =
      bothRestrictions (classIntersection a (domain R)) R
        (classIntersection b (converseDomain R)) := by
  funext x y
  apply propext
  change (a x ∧ R x y ∧ b y) ↔
    ((a x ∧ ∃ z, R x z) ∧ R x y ∧ (b y ∧ ∃ z, R z y))
  constructor
  · intro h
    exact ⟨⟨h.1, ⟨y, h.2.1⟩⟩, h.2.1, h.2.2, ⟨x, h.2.1⟩⟩
  · intro h
    exact ⟨h.1.1, h.2.1, h.2.2.1⟩

/-- PM I ✱35·354. -/
theorem star_35_354 (R : Relation α β) (b : Class β) (S : Relation β γ) :
    composition (rightRestriction R b) S = composition R (leftRestriction b S) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨hxy, hby⟩, hyz⟩
    exact ⟨y, hxy, hby, hyz⟩
  · rintro ⟨y, hxy, hby, hyz⟩
    exact ⟨y, ⟨hxy, hby⟩, hyz⟩

/-- PM I ✱35·41. -/
theorem star_35_41 (a a' : Class α) (R : Relation α β) :
    leftRestriction (classUnion a a') R =
      relationUnion (leftRestriction a R) (leftRestriction a' R) := by
  funext x y
  apply propext
  simp [leftRestriction, classUnion, relationUnion, or_and_right]

/-- PM I ✱35·412. -/
theorem star_35_412 (R : Relation α β) (b b' : Class β) :
    rightRestriction R (classUnion b b') =
      relationUnion (rightRestriction R b) (rightRestriction R b') := by
  funext x y
  apply propext
  simp [rightRestriction, classUnion, relationUnion, and_or_left]

/-- PM I ✱35·413. -/
theorem star_35_413 (a a' : Class α) (R : Relation α β) (b b' : Class β) :
    bothRestrictions (classUnion a a') R (classUnion b b') =
      relationUnion
        (relationUnion (bothRestrictions a R b) (bothRestrictions a R b'))
        (relationUnion (bothRestrictions a' R b) (bothRestrictions a' R b')) := by
  funext x y
  apply propext
  change ((a x ∨ a' x) ∧ R x y ∧ (b y ∨ b' y)) ↔
    ((a x ∧ R x y ∧ b y ∨ a x ∧ R x y ∧ b' y) ∨
      (a' x ∧ R x y ∧ b y ∨ a' x ∧ R x y ∧ b' y))
  constructor
  · rintro ⟨ha, hR, hb⟩
    cases ha with
    | inl ha =>
        cases hb with
        | inl hb => exact Or.inl (Or.inl ⟨ha, hR, hb⟩)
        | inr hb => exact Or.inl (Or.inr ⟨ha, hR, hb⟩)
    | inr ha =>
        cases hb with
        | inl hb => exact Or.inr (Or.inl ⟨ha, hR, hb⟩)
        | inr hb => exact Or.inr (Or.inr ⟨ha, hR, hb⟩)
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact ⟨Or.inl h.1, h.2.1, Or.inl h.2.2⟩
      · exact ⟨Or.inl h.1, h.2.1, Or.inr h.2.2⟩
    · rcases h with h | h
      · exact ⟨Or.inr h.1, h.2.1, Or.inl h.2.2⟩
      · exact ⟨Or.inr h.1, h.2.1, Or.inr h.2.2⟩

end PM.Architecture.Star35DomainUnionKernel
