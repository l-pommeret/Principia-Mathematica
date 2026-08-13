namespace PM.Architecture.Star32ConsecutiveKernel2

universe u v

abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

def rightSection (R : RelationExtension α β) (y : β) : ClassExtension α :=
  fun x => R x y

def leftSection (R : RelationExtension α β) (x : α) : ClassExtension β :=
  fun y => R x y

def rightSectionMap (R : RelationExtension α β) : β → ClassExtension α :=
  fun y => rightSection R y

def leftSectionMap (R : RelationExtension α β) : α → ClassExtension β :=
  fun x => leftSection R x

private theorem relationOfRightSections {R S : RelationExtension α β}
    (h : rightSectionMap R = rightSectionMap S) : R = S := by
  funext x y
  have hs := congrFun h y
  exact congrFun hs x

private theorem relationOfLeftSections {R S : RelationExtension α β}
    (h : leftSectionMap R = leftSectionMap S) : R = S := by
  funext x y
  have hs := congrFun h x
  exact congrFun hs y

/-- PM I ✱32·14. -/
theorem star_32_14 (R S : RelationExtension α β) :
    rightSectionMap R = rightSectionMap S ↔ R = S := by
  constructor
  · exact relationOfRightSections
  · intro h
    cases h
    rfl

/-- PM I ✱32·15. -/
theorem star_32_15 (R S : RelationExtension α β) :
    leftSectionMap R = leftSectionMap S ↔ R = S := by
  constructor
  · exact relationOfLeftSections
  · intro h
    cases h
    rfl

/-- PM I ✱32·16: all three printed identities are equivalent. -/
theorem star_32_16 (R S : RelationExtension α β) :
    (rightSectionMap R = rightSectionMap S ↔
      leftSectionMap R = leftSectionMap S) ∧
    (leftSectionMap R = leftSectionMap S ↔ R = S) := by
  exact ⟨(star_32_14 R S).trans (star_32_15 R S).symm, star_32_15 R S⟩

/-- PM I ✱32·18. -/
theorem star_32_18 (R : RelationExtension α β) (x : α) (y : β) :
    rightSection R y x ↔ R x y := Iff.rfl

/-- PM I ✱32·181. -/
theorem star_32_181 (R : RelationExtension α β) (x : α) (y : β) :
    leftSection R x y ↔ R x y := Iff.rfl

/-- PM I ✱32·182. -/
theorem star_32_182 (R : RelationExtension α β) (x : α) (y : β) :
    rightSection R y x ↔ leftSection R x y := Iff.rfl

/-- PM I ✱32·19: relation inclusion gives both sectional inclusions. -/
theorem star_32_19 (R S : RelationExtension α β)
    (h : ∀ x y, R x y → S x y) :
    (∀ y x, rightSection R y x → rightSection S y x) ∧
    (∀ x y, leftSection R x y → leftSection S x y) := by
  exact ⟨fun y x => h x y, fun x y => h x y⟩

/-- PM I ✱32·2, application of the right-sectional map. -/
theorem star_32_2 (R : RelationExtension α β)
    (A : β → ClassExtension α) :
    (A = rightSectionMap R) ↔ A = fun y x => R x y := Iff.rfl

/-- PM I ✱32·201, application of the left-sectional map. -/
theorem star_32_201 (R : RelationExtension α β)
    (A : α → ClassExtension β) :
    (A = leftSectionMap R) ↔ A = fun x y => R x y := Iff.rfl

/-- PM I ✱32·21. -/
theorem star_32_21 (R : RelationExtension α β) :
    rightSectionMap R = fun y x => R x y := rfl

end PM.Architecture.Star32ConsecutiveKernel2
