namespace PM.Architecture.Star35InclusionRecoveryKernel

universe u v

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def leftRestriction (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y

def rightRestriction (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y

def bothRestrictions (a : Class α) (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => a x ∧ R x y ∧ b y

def classIncluded (a b : Class α) : Prop := ∀ x, a x → b x
def relationIncluded (R S : Relation α β) : Prop := ∀ x y, R x y → S x y
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def converseDomain (R : Relation α β) : Class β := fun y => ∃ x, R x y

/-- PM I ✱35·442. -/
theorem star_35_442 (a : Class α) (R : Relation α β) (b : Class β) :
    relationIncluded (bothRestrictions a R b) R := by
  intro x y h
  exact h.2.1

/-- PM I ✱35·451. -/
theorem star_35_451 (R : Relation α β) (a : Class α)
    (h : classIncluded (domain R) a) :
    leftRestriction a R = R := by
  funext x y
  apply propext
  constructor
  · exact fun hxy => hxy.2
  · intro hxy
    exact ⟨h x ⟨y, hxy⟩, hxy⟩

/-- PM I ✱35·452. -/
theorem star_35_452 (R : Relation α β) (b : Class β)
    (h : classIncluded (converseDomain R) b) :
    rightRestriction R b = R := by
  funext x y
  apply propext
  constructor
  · exact fun hxy => hxy.1
  · intro hxy
    exact ⟨hxy, h y ⟨x, hxy⟩⟩

/-- PM I ✱35·453. -/
theorem star_35_453 (R : Relation α β) (a : Class α) (b : Class β)
    (h : classIncluded (domain R) a) :
    bothRestrictions a R b = rightRestriction R b := by
  funext x y
  apply propext
  constructor
  · intro hxy
    exact ⟨hxy.2.1, hxy.2.2⟩
  · intro hxy
    exact ⟨h x ⟨y, hxy.1⟩, hxy.1, hxy.2⟩

/-- PM I ✱35·454. -/
theorem star_35_454 (R : Relation α β) (a : Class α) (b : Class β)
    (h : classIncluded (converseDomain R) b) :
    bothRestrictions a R b = leftRestriction a R := by
  funext x y
  apply propext
  constructor
  · intro hxy
    exact ⟨hxy.1, hxy.2.1⟩
  · intro hxy
    exact ⟨hxy.1, hxy.2, h y ⟨x, hxy.2⟩⟩

/-- PM I ✱35·46. -/
theorem star_35_46 (R S : Relation α β) (a : Class α)
    (h : relationIncluded R S) :
    relationIncluded (leftRestriction a R) (leftRestriction a S) := by
  intro x y hxy
  exact ⟨hxy.1, h x y hxy.2⟩

/-- PM I ✱35·461. -/
theorem star_35_461 (R S : Relation α β) (b : Class β)
    (h : relationIncluded R S) :
    relationIncluded (rightRestriction R b) (rightRestriction S b) := by
  intro x y hxy
  exact ⟨h x y hxy.1, hxy.2⟩

/-- PM I ✱35·462. -/
theorem star_35_462 (R S : Relation α β) (a : Class α) (b : Class β)
    (h : relationIncluded R S) :
    relationIncluded (bothRestrictions a R b) (bothRestrictions a S b) := by
  intro x y hxy
  exact ⟨hxy.1, h x y hxy.2.1, hxy.2.2⟩

end PM.Architecture.Star35InclusionRecoveryKernel
