namespace PM.Architecture.Star20Q314Definitions

/-!
# PM I ✱20·01–✱20·02

Classes remain eliminative incomplete symbols. `ClassContext α` is what PM
writes as a context `f{--}` accepting a predicative matrix; no class object or
set-theoretic membership primitive is introduced.
-/

/-- An arbitrary one-place propositional matrix `ψ`. -/
structure Matrix (α : Type) where
  apply : α → Prop

/-- The explicitly predicative one-place matrix quantified as `φ!` by PM. -/
structure PredicativeMatrix (α : Type) where
  apply : α → Prop

/-- Extensional agreement `φ!x ≡ₓ ψx`. -/
def ExtensionallyEquivalent (φ : PredicativeMatrix α) (ψ : Matrix α) : Prop :=
  ∀ x, φ.apply x ↔ ψ.apply x

/-- An open propositional context accepting the extension of a predicative
matrix. This is an eliminator, not a type of classes. -/
abbrev ClassContext (α : Type) := PredicativeMatrix α → Prop

/-- ✱20·01: `f{ẑ(ψz)}` is defined by existentially choosing a predicative
matrix extensionally equivalent to `ψ` and applying the context to it. -/
def star_20_01 (f : ClassContext α) (ψ : Matrix α) : Prop :=
  ∃ φ : PredicativeMatrix α, ExtensionallyEquivalent φ ψ ∧ f φ

/-- ✱20·02: membership in the extension of `φ!` reduces to `φ!x`. -/
def star_20_02 (x : α) (φ : PredicativeMatrix α) : Prop :=
  φ.apply x

end PM.Architecture.Star20Q314Definitions
