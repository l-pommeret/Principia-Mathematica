namespace PM.Architecture.Star20Q321Kernel

abbrev Class (α : Type u) := α → Prop

def extension (φ : α → Prop) : Class α := φ

def membership (x : α) (a : Class α) : Prop := a x

/-- The type-relative `Cls`: extensions of predicates of the appropriate
element type. -/
def Classes (α : Type u) : Class (Class α) :=
  fun a => ∃ φ : α → Prop, a = extension φ

/-- ✱20·35: equality is equivalent to indiscernibility with respect to
membership in every class of the relevant type. -/
theorem star_20_35 {α : Type u} (x y : α) :
    x = y ↔ ∀ a : Class α, (membership x a ↔ membership y a) := by
  constructor
  · rintro rfl a
    exact Iff.rfl
  · intro h
    have hyx : y = x := (h (fun z => z = x)).mp rfl
    exact hyx.symm

/-- ✱20·4: the literal unfolding of type-relative `Cls`. -/
theorem star_20_4 {α : Type u} (a : Class α) :
    membership a (Classes α) ↔ ∃ φ : α → Prop, a = extension φ := by
  rfl

/-- ✱20·41: every displayed extension belongs to `Cls`. -/
theorem star_20_41 {α : Type u} (ψ : α → Prop) :
    membership (extension ψ) (Classes α) := by
  exact ⟨ψ, rfl⟩

/-- ✱20·42: abstracting a class's membership condition recovers it. -/
theorem star_20_42 {α : Type u} (a : Class α) :
    extension (fun z => membership z a) = a := by
  rfl

/-- Contextual membership of `(℩x)(φx)` in the extension of `ψ`. -/
def DescriptionMembership {α : Type u} (φ ψ : α → Prop) : Prop :=
  ∃ b, (∀ x, φ x ↔ x = b) ∧ membership b (extension ψ)

/-- The corresponding contextual application `ψ{(℩x)(φx)}`. -/
def DescriptionApplication {α : Type u} (φ ψ : α → Prop) : Prop :=
  ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b

/-- ✱20·5: membership of a description is application of the class matrix
to the same contextual description. -/
theorem star_20_5 {α : Type u} (φ ψ : α → Prop) :
    DescriptionMembership φ ψ ↔ DescriptionApplication φ ψ := by
  rfl

end PM.Architecture.Star20Q321Kernel
