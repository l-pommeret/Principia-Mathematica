namespace PM.Architecture.Star35ConsecutiveKernel

universe u v

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def leftRestriction (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y

def rightRestriction (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y

def bothRestrictions (a : Class α) (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => a x ∧ R x y ∧ b y

def relationIntersection (R S : Relation α β) : Relation α β :=
  fun x y => R x y ∧ S x y

def classIntersection (a b : Class α) : Class α :=
  fun x => a x ∧ b x

/-- PM I ✱35·1. -/
theorem star_35_1 (a : Class α) (R : Relation α β) (x : α) (y : β) :
    leftRestriction a R x y ↔ a x ∧ R x y := Iff.rfl

/-- PM I ✱35·101. -/
theorem star_35_101 (R : Relation α β) (b : Class β) (x : α) (y : β) :
    rightRestriction R b x y ↔ R x y ∧ b y := Iff.rfl

/-- PM I ✱35·102. -/
theorem star_35_102 (a : Class α) (R : Relation α β) (b : Class β) (x : α) (y : β) :
    bothRestrictions a R b x y ↔ a x ∧ R x y ∧ b y := Iff.rfl

/-- PM I ✱35·103. -/
theorem star_35_103 (a : Class α) (b : Class β) (x : α) (y : β) :
    (a x ∧ b y) ↔ a x ∧ b y := Iff.rfl

/-- PM I ✱35·11. -/
theorem star_35_11 (a : Class α) (R : Relation α β) (b : Class β) :
    bothRestrictions a R b =
      relationIntersection (leftRestriction a R) (rightRestriction R b) := by
  funext x y
  apply propext
  change (a x ∧ R x y ∧ b y) ↔ ((a x ∧ R x y) ∧ R x y ∧ b y)
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.1, h.2.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, h.2.2⟩

/-- PM I ✱35·12. -/
theorem star_35_12 (a : Class α) (R S : Relation α β) (b : Class β) :
    relationIntersection (leftRestriction a R) (rightRestriction S b) =
      bothRestrictions a (relationIntersection R S) b := by
  funext x y
  apply propext
  simp [bothRestrictions, relationIntersection, leftRestriction, rightRestriction,
    and_left_comm, and_comm]

/-- PM I ✱35·13. -/
theorem star_35_13 (a a' : Class α) (R S : Relation α β) :
    relationIntersection (leftRestriction a R) (leftRestriction a' S) =
      leftRestriction (classIntersection a a') (relationIntersection R S) := by
  funext x y
  apply propext
  simp [relationIntersection, leftRestriction, classIntersection,
    and_left_comm, and_comm]

/-- PM I ✱35·14. -/
theorem star_35_14 (R S : Relation α β) (b b' : Class β) :
    relationIntersection (rightRestriction R b) (rightRestriction S b') =
      rightRestriction (relationIntersection R S) (classIntersection b b') := by
  funext x y
  apply propext
  simp [relationIntersection, rightRestriction, classIntersection,
    and_left_comm, and_comm]

/-- PM I ✱35·15. -/
theorem star_35_15 (a a' : Class α) (R S : Relation α β) (b b' : Class β) :
    relationIntersection (bothRestrictions a R b) (bothRestrictions a' S b') =
      bothRestrictions (classIntersection a a') (relationIntersection R S)
        (classIntersection b b') := by
  funext x y
  apply propext
  simp [bothRestrictions, relationIntersection, classIntersection,
    and_left_comm, and_comm]

/-- PM I ✱35·16, retaining both printed equalities. -/
theorem star_35_16 (a : Class α) (R S : Relation α β) :
    relationIntersection (leftRestriction a R) S =
        leftRestriction a (relationIntersection R S) ∧
      leftRestriction a (relationIntersection R S) =
        relationIntersection R (leftRestriction a S) := by
  constructor <;> funext x y <;> apply propext <;>
    simp [relationIntersection, leftRestriction, and_left_comm, and_comm]

/-- PM I ✱35·17, retaining both printed equalities. -/
theorem star_35_17 (R S : Relation α β) (b : Class β) :
    relationIntersection (rightRestriction R b) S =
        rightRestriction (relationIntersection R S) b ∧
      rightRestriction (relationIntersection R S) b =
        relationIntersection R (rightRestriction S b) := by
  constructor <;> funext x y <;> apply propext <;>
    simp [relationIntersection, rightRestriction, and_left_comm, and_comm]

/-- PM I ✱35·18, retaining both printed equalities. -/
theorem star_35_18 (a : Class α) (R S : Relation α β) (b : Class β) :
    relationIntersection (bothRestrictions a R b) S =
        bothRestrictions a (relationIntersection R S) b ∧
      bothRestrictions a (relationIntersection R S) b =
        relationIntersection R (bothRestrictions a S b) := by
  constructor <;> funext x y <;> apply propext <;>
    simp [bothRestrictions, relationIntersection, and_left_comm, and_comm]

end PM.Architecture.Star35ConsecutiveKernel
