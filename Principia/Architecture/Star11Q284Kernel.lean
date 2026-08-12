/-!
# PM I, ✱11·46, ✱11·47, ✱11·5, ✱11·51, ✱11·52

Exact propositions obtained by reading the two apparent variables as the two
explicit binders below.  `Nonempty α` and `Nonempty β` in ✱11·46 and ✱11·47
make explicit PM's convention that every type has possible arguments; they
are necessary for the reverse implications when `p` is false.
-/

namespace PM.Architecture.Star11Q284Kernel

/-- ✱11·46. Existential quantification commutes with an implication whose
antecedent is independent of both apparent variables. -/
theorem star_11_46 {α β : Sort _} [Nonempty α] [Nonempty β]
    (p : Prop) (φ : α → β → Prop) :
    (∃ x y, p → φ x y) ↔ (p → ∃ x y, φ x y) := by
  classical
  constructor
  · rintro ⟨x, y, h⟩ hp
    exact ⟨x, y, h hp⟩
  · intro h
    by_cases hp : p
    · obtain ⟨x, y, hxy⟩ := h hp
      exact ⟨x, y, fun _ => hxy⟩
    · exact ⟨Classical.choice inferInstance, Classical.choice inferInstance,
        fun hp' => (hp hp').elim⟩

/-- ✱11·47. Universal quantification commutes with conjunction by a
proposition independent of both apparent variables. -/
theorem star_11_47 {α β : Sort _} [Nonempty α] [Nonempty β]
    (p : Prop) (φ : α → β → Prop) :
    (∀ x y, p ∧ φ x y) ↔ (p ∧ ∀ x y, φ x y) := by
  constructor
  · intro h
    let x : α := Classical.choice inferInstance
    let y : β := Classical.choice inferInstance
    exact ⟨(h x y).1, fun a b => (h a b).2⟩
  · rintro ⟨hp, hφ⟩ x y
    exact ⟨hp, hφ x y⟩

/-- ✱11·5. The three printed forms of existential negation for a binary
propositional function are equivalent. -/
theorem star_11_5 {α β : Sort _} (φ : α → β → Prop) :
    ((∃ x, ¬ ∀ y, φ x y) ↔ ¬ ∀ x y, φ x y) ∧
    ((¬ ∀ x y, φ x y) ↔ ∃ x y, ¬ φ x y) := by
  classical
  constructor
  · constructor
    · rintro ⟨x, hx⟩ hall
      exact hx (hall x)
    · intro h
      exact Classical.byContradiction fun hn =>
        h (fun x => Classical.byContradiction fun hx => hn ⟨x, hx⟩)
  · constructor
    · intro h
      exact Classical.byContradiction fun hn =>
        h (fun x y => Classical.byContradiction fun hxy => hn ⟨x, y, hxy⟩)
    · rintro ⟨x, y, hxy⟩ hall
      exact hxy (hall x y)

/-- ✱11·51. A mixed existential/universal assertion is the negation of its
dual universal/existential assertion. -/
theorem star_11_51 {α β : Sort _} (φ : α → β → Prop) :
    (∃ x, ∀ y, φ x y) ↔ ¬ ∀ x, ∃ y, ¬ φ x y := by
  classical
  constructor
  · rintro ⟨x, hx⟩ hdual
    obtain ⟨y, hy⟩ := hdual x
    exact hy (hx y)
  · intro h
    exact Classical.byContradiction fun hn =>
      h (fun x => Classical.byContradiction fun hx =>
        hn ⟨x, fun y => Classical.byContradiction fun hxy => hx ⟨y, hxy⟩⟩)

/-- ✱11·52. Negating the universal implication gives exactly an existential
counterexample in which both matrices hold. -/
theorem star_11_52 {α β : Sort _} (φ ψ : α → β → Prop) :
    (∃ x y, φ x y ∧ ψ x y) ↔ ¬ ∀ x y, φ x y → ¬ ψ x y := by
  classical
  constructor
  · rintro ⟨x, y, hφ, hψ⟩ hall
    exact hall x y hφ hψ
  · intro h
    exact Classical.byContradiction fun hn =>
      h (fun x y hφ => fun hψ => hn ⟨x, y, hφ, hψ⟩)

end PM.Architecture.Star11Q284Kernel
