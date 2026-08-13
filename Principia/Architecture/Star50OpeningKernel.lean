namespace PM.Architecture.Star50OpeningKernel

universe u

abbrev Relation (α : Sort u) := α → α → Prop
abbrev ClassExtension (α : Sort u) := α → Prop

/-- PM I ✱50·01. -/
def I : Relation α := fun x y => x = y

/-- PM I ✱50·02. -/
def J : Relation α := fun x y => ¬ I x y

/-- PM I ✱50·1. -/
theorem star_50_1 (x y : α) : I x y ↔ x = y := Iff.rfl

/-- PM I ✱50·11. -/
theorem star_50_11 (x y : α) : J x y ↔ x ≠ y := Iff.rfl

/-- PM I ✱50·12. -/
theorem star_50_12 : (J : Relation α) = fun x y => x ≠ y := rfl

/-- PM I ✱50·13: the identity relation is inhabited whenever its assigned
type is inhabited. -/
theorem star_50_13 [Nonempty α] : ∃ x y : α, I x y := by
  let ⟨x⟩ := (inferInstance : Nonempty α)
  exact ⟨x, x, rfl⟩

/-- PM I ✱50·14: the unique value of the identity fibre at `y` is `y`. -/
theorem star_50_14 (y : α) :
    ∃ x, I x y ∧ x = y ∧ ∀ z, I z y → z = x := by
  exact ⟨y, rfl, rfl, fun z hz => hz⟩

/-- PM I ✱50·15: every identity fibre has exactly one member. -/
theorem star_50_15 (y : α) :
    ∃ x, I x y ∧ ∀ z, I z y → z = x := by
  exact ⟨y, rfl, fun z hz => hz⟩

def image (R : Relation α) (A : ClassExtension α) : ClassExtension α :=
  fun x => ∃ y, A y ∧ R x y

private theorem classExt {A B : ClassExtension α} (h : ∀ x, A x ↔ B x) :
    A = B := by
  funext x
  exact propext (h x)

/-- PM I ✱50·16. -/
theorem star_50_16 (A : ClassExtension α) : image I A = A := by
  apply classExt
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- PM I ✱50·17.  `UniqueAt R x x` is the contextual reading of `Rʻx = x`. -/
theorem star_50_17 (R : Relation α) (A : ClassExtension α)
    (h : ∀ x, A x → R x x ∧ ∀ z, R z x → z = x) :
    image R A = A := by
  apply classExt
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : x = y := (h y hy).2 x hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, (h x hx).1⟩

end PM.Architecture.Star50OpeningKernel
