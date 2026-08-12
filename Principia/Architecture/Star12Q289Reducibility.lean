/-!
# PM I ✱12·1 and ✱12·11 — reducibility in the Lean embedding

PM states these as primitive propositions because its ramified hierarchy
distinguishes an arbitrary function from a predicative function.  Lean's
function space is already extensional and unramified.  `Predicative₁` and
`Predicative₂` below name the target function sorts of the embedding; the
canonical witnesses are therefore the matrices themselves.  No new axiom is
introduced.
-/

namespace PM.Architecture.Star12Q289Reducibility

/-- Unary predicative propositional functions in the Lean embedding. -/
abbrev Predicative₁ (α : Sort _) := α → Prop

/-- Binary predicative propositional functions in the Lean embedding. -/
abbrev Predicative₂ (α : Sort _) (β : Sort _) := α → β → Prop

/-- ✱12·1, the unary axiom of reducibility: a predicative function exists
which is formally equivalent to the given propositional function. -/
theorem star_12_1 {α : Sort _} (φ : α → Prop) :
    ∃ f : Predicative₁ α, ∀ x, φ x ↔ f x :=
  ⟨φ, fun _ => Iff.rfl⟩

/-- ✱12·11, the binary axiom of reducibility. -/
theorem star_12_11 {α β : Sort _} (φ : α → β → Prop) :
    ∃ f : Predicative₂ α β, ∀ x y, φ x y ↔ f x y :=
  ⟨φ, fun _ _ => Iff.rfl⟩

end PM.Architecture.Star12Q289Reducibility
