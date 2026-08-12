/-! Exact null- and universal-class kernels for PM I, Q361. -/

namespace PM.Architecture.Star24Q361Kernel

abbrev Class (Object : Sort u) := Object → Prop

/-- PM I ✱24·01's universal class in the extensional embedding. -/
def Universal (Object : Sort u) : Class Object := fun _ => True

/-- PM I ✱24·02's null class. -/
def Null (Object : Sort u) : Class Object := fun _ => False

/-- PM I ✱24·102. -/
theorem star_24_102 (φ : Class Object) :
    (∀ x, φ x) ↔ φ = Universal Object := by
  constructor
  · intro h
    funext x
    exact propext ⟨fun _ => True.intro, fun _ => h x⟩
  · rintro rfl x
    trivial

/-- PM I ✱24·103. -/
theorem star_24_103 (φ : Class Object) :
    (∀ x, ¬ φ x) ↔ φ = Null Object := by
  constructor
  · intro h
    funext x
    exact propext ⟨fun hx => (h x hx).elim, False.elim⟩
  · rintro rfl x
    exact id

/-- PM I ✱24·104. -/
theorem star_24_104 (x : Object) : Universal Object x :=
  True.intro

/-- PM I ✱24·105. -/
theorem star_24_105 (x : Object) : ¬ Null Object x :=
  id

/-- PM I ✱24·11. -/
theorem star_24_11 (α : Class Object) :
    ∀ x, α x → Universal Object x := by
  intro _ _
  trivial

end PM.Architecture.Star24Q361Kernel
