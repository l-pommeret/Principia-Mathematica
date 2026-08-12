/-!
# PM I, ✱13·181–✱13·191

Exact polymorphic equality readings of the five printed propositions.
-/

namespace PM.Architecture.Star13Q293Kernel

/-- ✱13·181. Equality transports inequality in the printed orientation. -/
theorem star_13_181 {α : Sort _} (x y z : α) :
    x = y → y ≠ z → x ≠ z := by
  rintro rfl hyz
  exact hyz

/-- ✱13·182. Equality transports equality in the right argument. -/
theorem star_13_182 {α : Sort _} (x y z : α) :
    x = y → (z = x ↔ z = y) := by
  rintro rfl
  exact Iff.rfl

/-- ✱13·183. Equality is equivalent to formal equivalence, for every
`z`, of `z = x` and `z = y`. -/
theorem star_13_183 {α : Sort _} (x y : α) :
    x = y ↔ ∀ z, (z = x ↔ z = y) := by
  constructor
  · rintro rfl z
    exact Iff.rfl
  · intro h
    exact (h x).mp rfl

/-- ✱13·19. Every object has an object identical with it. -/
theorem star_13_19 {α : Sort _} (x : α) : ∃ y, y = x :=
  ⟨x, rfl⟩

/-- ✱13·191. Universal identity elimination at `x` is equivalent to the
matrix at `x`. -/
theorem star_13_191 {α : Sort _} (x : α) (φ : α → Prop) :
    (∀ y, y = x → φ y) ↔ φ x := by
  constructor
  · intro h
    exact h x rfl
  · intro hx y hy
    simpa [hy] using hx

end PM.Architecture.Star13Q293Kernel
