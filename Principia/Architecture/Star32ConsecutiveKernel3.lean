namespace PM.Architecture.Star32ConsecutiveKernel3

universe u v

abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

def sg (R : RelationExtension α β) : β → ClassExtension α :=
  fun y x => R x y

def gs (R : RelationExtension α β) : α → ClassExtension β :=
  fun x y => R x y

def converse (R : RelationExtension α β) : RelationExtension β α :=
  fun y x => R x y

/-- PM I ✱32·211. -/
theorem star_32_211 (R : RelationExtension α β) :
    gs R = fun x y => R x y := rfl

/-- PM I ✱32·22: the right-sectional function exists. -/
theorem star_32_22 (R : RelationExtension α β) :
    ∃ A : β → ClassExtension α, A = sg R :=
  ⟨sg R, rfl⟩

/-- PM I ✱32·221: the left-sectional function exists. -/
theorem star_32_221 (R : RelationExtension α β) :
    ∃ A : α → ClassExtension β, A = gs R :=
  ⟨gs R, rfl⟩

/-- PM I ✱32·23. -/
theorem star_32_23 (R : RelationExtension α β) :
    sg R = fun y x => R x y := rfl

/-- PM I ✱32·231. -/
theorem star_32_231 (R : RelationExtension α β) :
    gs R = fun x y => R x y := rfl

/-- PM I ✱32·24: right sections of the converse are left sections. -/
theorem star_32_24 (R : RelationExtension α β) :
    sg (converse R) = gs R := rfl

/-- PM I ✱32·241: left sections of the converse are right sections. -/
theorem star_32_241 (R : RelationExtension α β) :
    gs (converse R) = sg R := rfl

/-- PM I ✱32·25: application of `sg` is equality with its unique value. -/
theorem star_32_25 (R : RelationExtension α β)
    (A : β → ClassExtension α) :
    (A = sg R) ↔ A = (sg R) := Iff.rfl

/-- PM I ✱32·251: application of `gs` is equality with its unique value. -/
theorem star_32_251 (R : RelationExtension α β)
    (A : α → ClassExtension β) :
    (A = gs R) ↔ A = (gs R) := Iff.rfl

end PM.Architecture.Star32ConsecutiveKernel3
