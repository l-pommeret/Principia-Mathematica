namespace PM.Architecture.Star35MonotonicityKernel

universe u v

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def leftRestriction (a : Class α) (R : Relation α β) : Relation α β :=
  fun x y => a x ∧ R x y

def rightRestriction (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => R x y ∧ b y

def bothRestrictions (a : Class α) (R : Relation α β) (b : Class β) : Relation α β :=
  fun x y => a x ∧ R x y ∧ b y

def relationUnion (R S : Relation α β) : Relation α β := fun x y => R x y ∨ S x y

def classIncluded (a b : Class α) : Prop := ∀ x, a x → b x
def relationIncluded (R S : Relation α β) : Prop := ∀ x y, R x y → S x y

/-- PM I ✱35·42. -/
theorem star_35_42 (a : Class α) (R S : Relation α β) :
    leftRestriction a (relationUnion R S) =
      relationUnion (leftRestriction a R) (leftRestriction a S) := by
  funext x y
  apply propext
  change (a x ∧ (R x y ∨ S x y)) ↔ (a x ∧ R x y) ∨ (a x ∧ S x y)
  exact and_or_left

/-- PM I ✱35·421. -/
theorem star_35_421 (R S : Relation α β) (b : Class β) :
    rightRestriction (relationUnion R S) b =
      relationUnion (rightRestriction R b) (rightRestriction S b) := by
  funext x y
  apply propext
  change ((R x y ∨ S x y) ∧ b y) ↔ (R x y ∧ b y) ∨ (S x y ∧ b y)
  exact or_and_right

/-- PM I ✱35·422. -/
theorem star_35_422 (a : Class α) (R S : Relation α β) (b : Class β) :
    bothRestrictions a (relationUnion R S) b =
      relationUnion (bothRestrictions a R b) (bothRestrictions a S b) := by
  funext x y
  apply propext
  change (a x ∧ (R x y ∨ S x y) ∧ b y) ↔
    (a x ∧ R x y ∧ b y) ∨ (a x ∧ S x y ∧ b y)
  constructor
  · rintro ⟨ha, h, hb⟩
    cases h with
    | inl hR => exact Or.inl ⟨ha, hR, hb⟩
    | inr hS => exact Or.inr ⟨ha, hS, hb⟩
  · rintro (h | h)
    · exact ⟨h.1, Or.inl h.2.1, h.2.2⟩
    · exact ⟨h.1, Or.inr h.2.1, h.2.2⟩

/-- PM I ✱35·43. -/
theorem star_35_43 (a b : Class α) (R : Relation α β)
    (h : classIncluded a b) :
    relationIncluded (leftRestriction a R) (leftRestriction b R) := by
  intro x y hxy
  exact ⟨h x hxy.1, hxy.2⟩

/-- PM I ✱35·431. -/
theorem star_35_431 (R : Relation α β) (b c : Class β)
    (h : classIncluded b c) :
    relationIncluded (rightRestriction R b) (rightRestriction R c) := by
  intro x y hxy
  exact ⟨hxy.1, h y hxy.2⟩

/-- PM I ✱35·432. -/
theorem star_35_432 (a c : Class α) (b d : Class β) (R : Relation α β)
    (hac : classIncluded a c) (hbd : classIncluded b d) :
    relationIncluded (bothRestrictions a R b) (bothRestrictions c R d) := by
  intro x y hxy
  exact ⟨hac x hxy.1, hxy.2.1, hbd y hxy.2.2⟩

/-- PM I ✱35·44. -/
theorem star_35_44 (a : Class α) (R : Relation α β) :
    relationIncluded (leftRestriction a R) R := by
  intro x y hxy
  exact hxy.2

/-- PM I ✱35·441. -/
theorem star_35_441 (R : Relation α β) (b : Class β) :
    relationIncluded (rightRestriction R b) R := by
  intro x y hxy
  exact hxy.1

end PM.Architecture.Star35MonotonicityKernel
