namespace PM.Architecture.Star32ConsecutiveKernel

universe u v

abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

/-- PM's right and left sectional descriptive functions, in the explicit
simple-type interpretation of relation and class extensions. -/
def rightSection (R : RelationExtension α β) (y : β) : ClassExtension α :=
  fun x => R x y

def leftSection (R : RelationExtension α β) (x : α) : ClassExtension β :=
  fun y => R x y

/-- PM I ✱32·1. -/
theorem star_32_1 (R : RelationExtension α β) (A : ClassExtension α) (y : β) :
    (A = rightSection R y) ↔ A = fun x => R x y := Iff.rfl

/-- PM I ✱32·101. -/
theorem star_32_101 (R : RelationExtension α β) (B : ClassExtension β) (x : α) :
    (B = leftSection R x) ↔ B = fun y => R x y := Iff.rfl

/-- PM I ✱32·11. -/
theorem star_32_11 (R : RelationExtension α β) (y : β) :
    (fun x => R x y) = rightSection R y := rfl

/-- PM I ✱32·111. -/
theorem star_32_111 (R : RelationExtension α β) (x : α) :
    (fun y => R x y) = leftSection R x := rfl

/-- PM I ✱32·12: the right section exists as a class extension. -/
theorem star_32_12 (R : RelationExtension α β) (y : β) :
    ∃ A : ClassExtension α, A = rightSection R y :=
  ⟨rightSection R y, rfl⟩

/-- PM I ✱32·121: the left section exists as a class extension. -/
theorem star_32_121 (R : RelationExtension α β) (x : α) :
    ∃ B : ClassExtension β, B = leftSection R x :=
  ⟨leftSection R x, rfl⟩

/-- PM I ✱32·13. -/
theorem star_32_13 (R : RelationExtension α β) (y : β) :
    rightSection R y = fun x => R x y := rfl

/-- PM I ✱32·131. -/
theorem star_32_131 (R : RelationExtension α β) (x : α) :
    leftSection R x = fun y => R x y := rfl

/-- PM I ✱32·132, retaining both printed equivalences. -/
theorem star_32_132 (R : RelationExtension α β) (A : ClassExtension α) (y : β) :
    (A = rightSection R y) ↔ A = (fun x => R x y) := by
  constructor <;> intro h
  · simpa [rightSection] using h
  · simpa [rightSection] using h

/-- PM I ✱32·133, retaining both printed equivalences. -/
theorem star_32_133 (R : RelationExtension α β) (B : ClassExtension β) (x : α) :
    (B = leftSection R x) ↔ B = (fun y => R x y) := by
  constructor <;> intro h
  · simpa [leftSection] using h
  · simpa [leftSection] using h

end PM.Architecture.Star32ConsecutiveKernel
