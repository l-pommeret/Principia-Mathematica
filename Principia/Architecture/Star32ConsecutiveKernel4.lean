namespace PM.Architecture.Star32ConsecutiveKernel4

universe u v

abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

def rightSection (R : RelationExtension α β) (y : β) : ClassExtension α :=
  fun x => R x y

def leftSection (R : RelationExtension α β) (x : α) : ClassExtension β :=
  fun y => R x y

def inter (R S : RelationExtension α β) : RelationExtension α β :=
  fun x y => R x y ∧ S x y

def union (R S : RelationExtension α β) : RelationExtension α β :=
  fun x y => R x y ∨ S x y

def compl (R : RelationExtension α β) : RelationExtension α β :=
  fun x y => ¬ R x y

def classInter (A B : ClassExtension α) : ClassExtension α :=
  fun x => A x ∧ B x

def classUnion (A B : ClassExtension α) : ClassExtension α :=
  fun x => A x ∨ B x

def classCompl (A : ClassExtension α) : ClassExtension α :=
  fun x => ¬ A x

/-- PM I ✱32·3. -/
theorem star_32_3 (R S : RelationExtension α β) (y : β) :
    rightSection (inter R S) y =
      classInter (rightSection R y) (rightSection S y) := rfl

/-- PM I ✱32·31, the left-sectional companion of ✱32·3. -/
theorem star_32_31 (R S : RelationExtension α β) (x : α) :
    leftSection (inter R S) x =
      classInter (leftSection R x) (leftSection S x) := rfl

/-- PM I ✱32·32. -/
theorem star_32_32 (R S : RelationExtension α β) (y : β) :
    rightSection (union R S) y =
      classUnion (rightSection R y) (rightSection S y) := rfl

/-- PM I ✱32·33, the left-sectional companion of ✱32·32. -/
theorem star_32_33 (R S : RelationExtension α β) (x : α) :
    leftSection (union R S) x =
      classUnion (leftSection R x) (leftSection S x) := rfl

/-- PM I ✱32·34. -/
theorem star_32_34 (R : RelationExtension α β) (y : β) :
    rightSection (compl R) y = classCompl (rightSection R y) := rfl

/-- PM I ✱32·35. -/
theorem star_32_35 (R : RelationExtension α β) (x : α) :
    leftSection (compl R) x = classCompl (leftSection R x) := rfl

/-- The exact unique-value condition used in ✱32·4. -/
def FunctionalAt (R : RelationExtension α β) (y : β) : Prop :=
  ∃ x, R x y ∧ ∀ z, R z y → z = x

/-- PM I ✱32·4: existence of the descriptive value is equivalent to a
nonempty, subsingleton right section. -/
theorem star_32_4 (R : RelationExtension α β) (y : β) :
    FunctionalAt R y ↔
      (∃ x, rightSection R y x) ∧
      ∀ x z, rightSection R y x → rightSection R y z → x = z := by
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨⟨x, hx⟩, fun a b ha hb => (hu a ha).trans (hu b hb).symm⟩
  · rintro ⟨⟨x, hx⟩, hu⟩
    exact ⟨x, hx, fun z hz => hu z x hz hx⟩

/-- A choice-free contextual value of a functional fibre. -/
structure FiberValue (R : RelationExtension α β) (y : β) where
  value : α
  holds : R value y
  unique : ∀ z, R z y → z = value

/-- PM I ✱32·41: under existence of the `S`-value, equality of right sections
is equivalent to equality of their contextual descriptive values. -/
theorem star_32_41 (R S : RelationExtension α β) (y : β)
    (r : FiberValue R y) (s : FiberValue S y) :
    rightSection R y = rightSection S y ↔ r.value = s.value := by
  constructor
  · intro h
    have hs : S r.value y := by
      have point := congrFun h r.value
      exact Eq.mp point r.holds
    exact s.unique r.value hs
  · intro hrs
    funext x
    apply propext
    constructor
    · intro hx
      have : x = r.value := r.unique x hx
      rw [this, hrs]
      exact s.holds
    · intro hx
      have : x = s.value := s.unique x hx
      rw [this, ← hrs]
      exact r.holds

end PM.Architecture.Star32ConsecutiveKernel4
