namespace PM.Architecture.Star32ConsecutiveKernel5

universe u v

abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

def rightSection (R : RelationExtension α β) (y : β) : ClassExtension α :=
  fun x => R x y

/-- Existence and uniqueness of the descriptive value `Rʻy`. -/
def FunctionalAt (R : RelationExtension α β) (y : β) : Prop :=
  ∃ x, R x y ∧ ∀ z, R z y → z = x

/-- PM I ✱32·42: equality of right sections transports existence and
uniqueness of the corresponding descriptive values. -/
theorem star_32_42 (R S : RelationExtension α β) (y : β) :
    rightSection R y = rightSection S y →
      (FunctionalAt R y ↔ FunctionalAt S y) := by
  intro h
  constructor
  · rintro ⟨x, hx, hu⟩
    have hxS : S x y := Eq.mp (congrFun h x) hx
    refine ⟨x, hxS, ?_⟩
    intro z hzS
    have hzR : R z y := Eq.mpr (congrFun h z) hzS
    exact hu z hzR
  · rintro ⟨x, hx, hu⟩
    have hxR : R x y := Eq.mpr (congrFun h x) hx
    refine ⟨x, hxR, ?_⟩
    intro z hzR
    have hzS : S z y := Eq.mp (congrFun h z) hzR
    exact hu z hzS

end PM.Architecture.Star32ConsecutiveKernel5
