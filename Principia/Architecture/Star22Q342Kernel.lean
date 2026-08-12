namespace PM.Architecture.Star22Q342Kernel

/-!
# PM I ✱22·51, ✱22·57, ✱22·52, ✱22·7, ✱22·5

Exact extensional class laws from the section summary. A class is its typed
membership predicate; intersection and union are pointwise conjunction and
disjunction.
-/

private def intersection (α β : ι → Prop) : ι → Prop :=
  fun x => α x ∧ β x

private def union (α β : ι → Prop) : ι → Prop :=
  fun x => α x ∨ β x

/-- ✱22·51: commutativity of class intersection. -/
theorem star_22_51 (α β : ι → Prop) :
    intersection α β = intersection β α := by
  funext x
  apply propext
  exact and_comm

/-- ✱22·57: commutativity of class union. -/
theorem star_22_57 (α β : ι → Prop) :
    union α β = union β α := by
  funext x
  apply propext
  exact or_comm

/-- ✱22·52: associativity of class intersection, with the exact printed
parenthesization. -/
theorem star_22_52 (α β γ : ι → Prop) :
    intersection (intersection α β) γ =
      intersection α (intersection β γ) := by
  funext x
  apply propext
  exact and_assoc

/-- ✱22·7: associativity of class union, with the exact printed
parenthesization. -/
theorem star_22_7 (α β γ : ι → Prop) :
    union (union α β) γ = union α (union β γ) := by
  funext x
  apply propext
  exact or_assoc

/-- ✱22·5: idempotence of class intersection. -/
theorem star_22_5 (α : ι → Prop) :
    intersection α α = α := by
  funext x
  apply propext
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

end PM.Architecture.Star22Q342Kernel
