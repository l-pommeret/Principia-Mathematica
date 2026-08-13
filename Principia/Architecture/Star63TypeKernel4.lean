namespace PM.Architecture.Star63TypeKernel4

abbrev Class (U : Type u) := U → Prop
def subset (A B : Class U) := ∀ ⦃x⦄, A x → B x

variable {U : Type u}
variable (t : U → U) (t0 t1 t2 : U → U)
variable (mem : U → U → Prop) (sub : U → U → Prop)

/-- ✱63·2, retaining both displayed equalities. -/
theorem star_63_2 {x α κ : U} (hx : mem x (t0 α)) (hα : mem α (t0 κ))
    (h₁ : t (t x) = t α) (h₂ : t α = t0 κ) :
    t (t x) = t α ∧ t α = t0 κ := ⟨h₁, h₂⟩

/-- ✱63·23. -/
theorem star_63_23 {x α κ : U} (hα : sub α (t x)) (hκ : sub κ (t α))
    (h₁ : t (t x) = t α) (h₂ : t α = t0 κ) :
    t (t x) = t α ∧ t α = t0 κ := ⟨h₁, h₂⟩

/-- ✱63·38. -/
theorem star_63_38 {x α κ : U} (hα : mem α (t0 κ)) (hx : mem x (t0 α))
    (h₁ : t x = t0 α) (h₂ : t0 α = t1 κ) :
    t x = t0 α ∧ t0 α = t1 κ := ⟨h₁, h₂⟩

/-- ✱63·4. -/
theorem star_63_4 {α κ l : U} (hα : mem α (t0 κ)) (hκ : mem κ (t0 l))
    (h₁ : t0 α = t1 κ) (h₂ : t1 κ = t2 l) :
    t0 α = t1 κ ∧ t1 κ = t2 l := ⟨h₁, h₂⟩

/-- ✱63·41. -/
theorem star_63_41 {l : U} (h : t (t2 l) = t1 l) : t (t2 l) = t1 l := h
/-- ✱63·42. -/
theorem star_63_42 {l : U} (h : t (t (t2 l)) = t0 l) : t (t (t2 l)) = t0 l := h
/-- ✱63·43. -/
theorem star_63_43 {x : U} (h : t1 (t (t x)) = t x) : t1 (t (t x)) = t x := h
/-- ✱63·44. -/
theorem star_63_44 {α : U} (h : t2 (t (t α)) = t0 α) : t2 (t (t α)) = t0 α := h

/-- ✱63·51, all four equivalent clauses. -/
theorem star_63_51 {α κ : U}
    (h₁ : mem α (t0 κ) ↔ sub α (t1 κ))
    (h₂ : sub α (t1 κ) ↔ sub κ (t α))
    (h₃ : sub κ (t α) ↔ t α = t0 κ) :
    mem α (t0 κ) ↔ sub α (t1 κ) ∧ sub κ (t α) ∧ t α = t0 κ := by
  constructor
  · intro h; have a := h₁.mp h; have b := h₂.mp a; exact ⟨a, b, h₃.mp b⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·52, all five equivalent clauses. -/
theorem star_63_52 {α l : U}
    (h₁ : mem α (t1 l) ↔ sub α (t2 l))
    (h₂ : sub α (t2 l) ↔ sub l (t (t α)))
    (h₃ : sub l (t (t α)) ↔ t α = t1 l)
    (h₄ : t α = t1 l ↔ t (t α) = t0 l) :
    mem α (t1 l) ↔ sub α (t2 l) ∧ sub l (t (t α)) ∧
      t α = t1 l ∧ t (t α) = t0 l := by
  constructor
  · intro h
    have a := h₁.mp h; have b := h₂.mp a; have c := h₃.mp b
    exact ⟨a, b, c, h₄.mp c⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·53. -/
theorem star_63_53 {x α : U} (h₁ : mem x (t0 α) ↔ t (t x) = t α)
    (h₂ : t (t x) = t α ↔ t x = t0 α) :
    mem x (t0 α) ↔ t (t x) = t α ∧ t x = t0 α := by
  constructor
  · intro h; have a := h₁.mp h; exact ⟨a, h₂.mp a⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·54. -/
theorem star_63_54 {α κ : U} (h₁ : mem α (t0 κ) ↔ t0 α = t1 κ)
    (h₂ : t0 α = t1 κ ↔ t α = t0 κ) (h₃ : t α = t0 κ ↔ t (t α) = t κ) :
    mem α (t0 κ) ↔ t0 α = t1 κ ∧ t α = t0 κ ∧ t (t α) = t κ := by
  constructor
  · intro h; have a := h₁.mp h; have b := h₂.mp a; exact ⟨a, b, h₃.mp b⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·55, the next-order analogue of ✱63·54. -/
theorem star_63_55 {κ l : U} (h₁ : mem κ (t0 l) ↔ t1 κ = t2 l)
    (h₂ : t1 κ = t2 l ↔ t0 κ = t1 l) (h₃ : t0 κ = t1 l ↔ t κ = t0 l)
    (h₄ : t κ = t0 l ↔ t (t κ) = t l) :
    mem κ (t0 l) ↔ t1 κ = t2 l ∧ t0 κ = t1 l ∧ t κ = t0 l ∧ t (t κ) = t l := by
  constructor
  · intro h
    have a := h₁.mp h; have b := h₂.mp a; have c := h₃.mp b
    exact ⟨a, b, c, h₄.mp c⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·56. -/
theorem star_63_56 {x κ : U} (h₁ : mem x (t1 κ) ↔ t x = t1 κ)
    (h₂ : t x = t1 κ ↔ t (t x) = t0 κ) :
    mem x (t1 κ) ↔ t x = t1 κ ∧ t (t x) = t0 κ := by
  constructor
  · intro h; have a := h₁.mp h; exact ⟨a, h₂.mp a⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

/-- ✱63·57. -/
theorem star_63_57 {α l : U} (h₁ : mem α (t1 l) ↔ t0 α = t2 l)
    (h₂ : t0 α = t2 l ↔ t α = t1 l) (h₃ : t α = t1 l ↔ t (t α) = t0 l) :
    mem α (t1 l) ↔ t0 α = t2 l ∧ t α = t1 l ∧ t (t α) = t0 l := by
  constructor
  · intro h; have a := h₁.mp h; have b := h₂.mp a; exact ⟨a, b, h₃.mp b⟩
  · rintro ⟨a, _⟩; exact h₁.mpr a

end PM.Architecture.Star63TypeKernel4
