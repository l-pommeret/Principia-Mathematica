import Principia.Architecture.Star116EighthKernel

namespace PM.Architecture.Star116FinalKernel
open Star116SecondKernel Star116FourthKernel Star116EighthKernel

abbrev Predicate (A : Type u) := A → Bool
abbrev Relation (A : Type u) (B : Type v) := A → B → Bool

theorem star_116_92_first (A : Type u) :
    CardinalClass (Relation A (Predicate A)) = CardinalExp Bool (A × Predicate A) :=
  star_116_83 A (Predicate A)

theorem star_116_92_second (A : Type u) :
    CardinalClass (Relation (Predicate A) (Predicate A)) =
      CardinalExp Bool (Predicate A × Predicate A) :=
  star_116_83 (Predicate A) (Predicate A)

theorem star_116_92 (A : Type u) :
    CardinalClass (Relation A (Predicate A)) = CardinalExp Bool (A × Predicate A) ∧
    CardinalClass (Relation (Predicate A) (Predicate A)) =
      CardinalExp Bool (Predicate A × Predicate A) :=
  ⟨star_116_92_first A, star_116_92_second A⟩

end PM.Architecture.Star116FinalKernel
