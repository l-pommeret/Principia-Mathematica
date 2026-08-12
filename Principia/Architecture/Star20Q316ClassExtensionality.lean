namespace PM.Architecture.Star20Q316ClassExtensionality

/-- Classes whose possible members all have the single type `α`. -/
abbrev TypedClass (α : Sort _) := α → Prop

/-- The typed membership reading of PM's `x ε α`. -/
def Member (x : α) (a : TypedClass α) : Prop := a x

/-- PM I ✱20·43. Two classes of the same type are equal exactly when they
have the same members of that type. -/
theorem star_20_43 {α : Sort _} (a b : TypedClass α) :
    a = b ↔ ∀ x, Member x a ↔ Member x b := by
  constructor
  · rintro rfl x
    exact Iff.rfl
  · intro h
    funext x
    exact propext (h x)

end PM.Architecture.Star20Q316ClassExtensionality
