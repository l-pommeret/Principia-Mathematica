/-! PM I ✱41·34–42: eight consecutive restriction and field laws. -/

namespace PM.Architecture.Star41RestrictionKernel

abbrev Class (α : Sort _) := α → Prop
abbrev Relation (α : Sort _) (β : Sort _) := α → β → Prop
abbrev RelationClass (α : Sort _) (β : Sort _) := Relation α β → Prop
abbrev ClassClass (α : Sort _) := Class α → Prop

def sumRelations (collection : RelationClass α β) : Relation α β :=
  fun x y => ∃ R, collection R ∧ R x y
def sumClasses (collection : ClassClass α) : Class α :=
  fun x => ∃ a, collection a ∧ a x
def productClasses (collection : ClassClass α) : Class α :=
  fun x => ∀ a, collection a → a x
def mapRelations (op : Relation α β → Relation γ δ)
    (collection : RelationClass α β) : RelationClass γ δ :=
  fun S => ∃ R, collection R ∧ S = op R
def mapClasses (op : Class α → Relation β γ)
    (collection : ClassClass α) : RelationClass β γ :=
  fun R => ∃ a, collection a ∧ R = op a

def leftRestrict (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y
def rightRestrict (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y
def bothRestrict (a : Class α) (R : Relation α α) : Relation α α :=
  fun x y => a x ∧ R x y ∧ a y
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def range (R : Relation α β) : Class β := fun y => ∃ x, R x y
def field (R : Relation α α) : Class α :=
  fun x => domain R x ∨ range R x
def domainClasses (collection : RelationClass α β) : ClassClass α :=
  fun a => ∃ R, collection R ∧ a = domain R
def rangeClasses (collection : RelationClass α β) : ClassClass β :=
  fun a => ∃ R, collection R ∧ a = range R
def fieldClasses (collection : RelationClass α α) : ClassClass α :=
  fun a => ∃ R, collection R ∧ a = field R
def subclass (a b : Class α) : Prop := ∀ x, a x → b x

/-- ✱41·34. Relational sum commutes with left restriction. -/
theorem star_41_34 (a : Class α) (collection : RelationClass α β) :
    sumRelations (mapRelations (leftRestrict a) collection) =
      leftRestrict a (sumRelations collection) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, ⟨R, hR, rfl⟩, ha, hxy⟩
    exact ⟨ha, R, hR, hxy⟩
  · rintro ⟨ha, R, hR, hxy⟩
    exact ⟨leftRestrict a R, ⟨R, hR, rfl⟩, ha, hxy⟩

/-- ✱41·341. Relational sum commutes with right restriction. -/
theorem star_41_341 (b : Class β) (collection : RelationClass α β) :
    sumRelations (mapRelations (fun R => rightRestrict R b) collection) =
      rightRestrict (sumRelations collection) b := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, ⟨R, hR, rfl⟩, hxy, hb⟩
    exact ⟨⟨R, hR, hxy⟩, hb⟩
  · rintro ⟨⟨R, hR, hxy⟩, hb⟩
    exact ⟨rightRestrict R b, ⟨R, hR, rfl⟩, hxy, hb⟩

/-- ✱41·342. Relational sum commutes with restriction at both ends. -/
theorem star_41_342 (a : Class α) (collection : RelationClass α α) :
    sumRelations (mapRelations (bothRestrict a) collection) =
      bothRestrict a (sumRelations collection) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, ⟨R, hR, rfl⟩, hx, hxy, hy⟩
    exact ⟨hx, ⟨R, hR, hxy⟩, hy⟩
  · rintro ⟨hx, ⟨R, hR, hxy⟩, hy⟩
    exact ⟨bothRestrict a R, ⟨R, hR, rfl⟩, hx, hxy, hy⟩

/-- ✱41·35. Summing the restrictions of a fixed relation to a class of
right-hand classes equals restriction to their class sum. -/
theorem star_41_35 (M : Relation α β) (collection : ClassClass β) :
    sumRelations (mapClasses (rightRestrict M) collection) =
      rightRestrict M (sumClasses collection) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hxy, hya⟩
    exact ⟨hxy, a, ha, hya⟩
  · rintro ⟨hxy, a, ha, hya⟩
    exact ⟨rightRestrict M a, ⟨a, ha, rfl⟩, hxy, hya⟩

/-- ✱41·351. The corresponding left-hand restriction law. -/
theorem star_41_351 (M : Relation α β) (collection : ClassClass α) :
    sumRelations (mapClasses (fun a => leftRestrict a M) collection) =
      leftRestrict (sumClasses collection) M := by
  funext x y
  apply propext
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hxa, hxy⟩
    exact ⟨⟨a, ha, hxa⟩, hxy⟩
  · rintro ⟨⟨a, ha, hxa⟩, hxy⟩
    exact ⟨leftRestrict a M, ⟨a, ha, rfl⟩, hxa, hxy⟩

/-- ✱41·4. The domain of a relational product lies in the product of the
domains of all member relations. -/
theorem star_41_4 (collection : RelationClass α β) :
    subclass (domain (fun x y => ∀ R, collection R → R x y))
      (productClasses (domainClasses collection)) := by
  rintro x ⟨y, hxy⟩ a ⟨R, hR, rfl⟩
  exact ⟨y, hxy R hR⟩

/-- ✱41·41. The corresponding converse-domain (range) inclusion. -/
theorem star_41_41 (collection : RelationClass α β) :
    subclass (range (fun x y => ∀ R, collection R → R x y))
      (productClasses (rangeClasses collection)) := by
  rintro y ⟨x, hxy⟩ a ⟨R, hR, rfl⟩
  exact ⟨x, hxy R hR⟩

/-- ✱41·42. The field of a relational product lies in the product of the
fields of all member relations. -/
theorem star_41_42 (collection : RelationClass α α) :
    subclass (field (fun x y => ∀ R, collection R → R x y))
      (productClasses (fieldClasses collection)) := by
  intro x hx a
  rintro ⟨R, hR, rfl⟩
  cases hx with
  | inl hd =>
      obtain ⟨y, hxy⟩ := hd
      exact Or.inl ⟨y, hxy R hR⟩
  | inr hr =>
      obtain ⟨y, hyx⟩ := hr
      exact Or.inr ⟨y, hyx R hR⟩

end PM.Architecture.Star41RestrictionKernel
