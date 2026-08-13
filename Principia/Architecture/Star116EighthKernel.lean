import Principia.Architecture.Star116SeventhKernel

namespace PM.Architecture.Star116EighthKernel
open Star116SecondKernel Star116ThirdKernel Star116FourthKernel Star116FifthKernel Star116SeventhKernel

abbrev Predicate (A : Type u) := A → Bool
abbrev Relation (A : Type u) (B : Type v) := A → B → Bool

def relationPairEquiv (A : Type u) (B : Type v) :
    TypeEquiv (Relation A B) (A × B → Bool) where
  toFun r p := r p.1 p.2
  invFun f a b := f (a,b)
  leftInv _ := rfl
  rightInv f := funext fun p => by cases p; rfl

theorem star_116_7 (A : Type u) : CardinalClass (Predicate A) = CardinalExp Bool A := rfl
theorem star_116_71 (p : Predicate A) (x : A) : (!p x) = true ↔ p x = false := by
  cases h : p x <;> decide
theorem star_116_711 (p q : Predicate A) (h : ∀ x, p x = q x) : p = q := funext h
theorem star_116_712 (p : Predicate A) : ∃ q : Predicate A, q = p := ⟨p, rfl⟩
theorem star_116_713 (p q : Predicate A) : p = q → q = p := Eq.symm
theorem star_116_714 (p : Predicate A) : ∃ q, q = p := ⟨p, rfl⟩
theorem star_116_715 (p : Predicate A) : ∃ q : Predicate A, q = p := ⟨p, rfl⟩
theorem star_116_72 (A : Type u) : CardinalClass (Predicate A) = CardinalExp Bool A := star_116_7 A
theorem star_116_8 (A : Type u) (B : Type v) :
    SimilarType (Relation A B) (A × B → Bool) := ⟨relationPairEquiv A B⟩
theorem star_116_81 (A : Type u) (B : Type v) : Injective (relationPairEquiv A B).toFun := by
  intro x y h
  rw [← (relationPairEquiv A B).leftInv x, ← (relationPairEquiv A B).leftInv y, h]
theorem star_116_82 (A : Type u) (B : Type v) :
    SimilarType (Relation A B) (A × B → Bool) := star_116_8 A B
theorem star_116_83 (A : Type u) (B : Type v) :
    CardinalClass (Relation A B) = CardinalExp Bool (A × B) := by
  rw [star_116_361 (star_116_82 A B)]
  rfl
theorem star_116_9 (A : Type u) : CardinalClass (Predicate A) = CardinalExp Bool A := star_116_72 A
theorem star_116_901 (A : Type u) : CardinalClass (Predicate A) = CardinalExp Bool A := star_116_9 A
theorem star_116_91 (A : Type u) :
    CardinalClass (Relation A A) = CardinalExp Bool (A × A) := star_116_83 A A

end PM.Architecture.Star116EighthKernel
