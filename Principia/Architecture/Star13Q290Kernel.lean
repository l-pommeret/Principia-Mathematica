namespace PM.Architecture.Star13Q290Kernel

/-- The predicative-function range implicit in PM I ✱13·01. -/
structure PredicativeRange (α : Type u) where
  Predicative : (α → Prop) → Prop

/-- The exact model interface supplied by the reducibility axiom ✱12·1. -/
structure Reducibility (range : PredicativeRange α) where
  reducibility : (ψ : α → Prop) →
    ∃ φ, range.Predicative φ ∧ ∀ x, ψ x ↔ φ x

/-- PM I ✱13·01: identity is indiscernibility with respect to every
predicative propositional function. -/
def star_13_01 (range : PredicativeRange α) (x y : α) : Prop :=
  ∀ φ, range.Predicative φ → φ x → φ y

/-- PM I ✱13·02: diversity is the negation of identity. -/
abbrev star_13_02 (range : PredicativeRange α) (x y : α) : Prop :=
  ¬ star_13_01 range x y

/-- PM I ✱13·03: chained identity abbreviates the conjunction of its two
adjacent identity propositions. -/
abbrev star_13_03 (range : PredicativeRange α) (x y z : α) : Prop :=
  star_13_01 range x y ∧ star_13_01 range y z

/-- PM I ✱13·1: the formal-implication reading of the identity definition. -/
theorem star_13_1 (range : PredicativeRange α) (x y : α) :
    star_13_01 range x y ↔
      ∀ φ, range.Predicative φ → φ x → φ y := by
  rfl

/-- PM I ✱13·101: substitution for an arbitrary propositional function.
The single use of `basis.reducibility` is exactly the printed ✱12·1 step. -/
theorem star_13_101 (range : PredicativeRange α)
    (reducibility : Reducibility range) (x y : α) (ψ : α → Prop) :
    star_13_01 range x y → ψ x → ψ y := by
  intro hxy hψx
  obtain ⟨φ, hφ, hreduce⟩ := reducibility.reducibility ψ
  exact (hreduce y).mpr (hxy φ hφ ((hreduce x).mp hψx))

end PM.Architecture.Star13Q290Kernel
