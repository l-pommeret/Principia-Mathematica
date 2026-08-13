import Principia.Architecture.Star116FifthKernel

namespace PM.Architecture.Star116SixthKernel
open Star116SecondKernel Star116FourthKernel Star116FifthKernel

def flipEquiv (A : Type u) (B : Type v) (C : Type w) :
    TypeEquiv (C → B → A) (B → C → A) where
  toFun f b c := f c b
  invFun f c b := f b c
  leftInv _ := rfl
  rightInv _ := rfl

theorem star_116_602 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := star_116_6 A B C
theorem star_116_603 (A : Type u) (B : Type v) (C : Type w) :
    (curryEquiv A B C).toFun ∘ (curryEquiv A B C).invFun = id := by
  funext f; exact (curryEquiv A B C).rightInv f
theorem star_116_604 (A : Type u) (B : Type v) (C : Type w) :
    (curryEquiv A B C).invFun ∘ (curryEquiv A B C).toFun = id := star_116_601 A B C
theorem star_116_605 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := ⟨curryEquiv A B C⟩
theorem star_116_606 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (C → B → A) (B → C → A) := ⟨flipEquiv A B C⟩
theorem star_116_607 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := star_116_6 A B C
theorem star_116_61 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (C → B → A) (B × C → A) := ⟨equivSymm (curryEquiv A B C)⟩
theorem star_116_611 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := star_116_6 A B C
theorem star_116_62 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := star_116_611 A B C
theorem star_116_63 (A : Type u) (B : Type v) (C : Type w) :
    CardinalClass (B × C → A) = CardinalClass (C → B → A) :=
  star_116_361 (star_116_62 A B C)
theorem star_116_64 (A : Type u) (B : Type v) (C : Type w) :
    CardinalClass (C → B → A) = CardinalClass (B → C → A) :=
  star_116_361 ⟨flipEquiv A B C⟩
theorem star_116_651 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_652 (e : TypeEquiv A B) : SimilarType B A := ⟨equivSymm e⟩
theorem star_116_653 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_361 ⟨e⟩
theorem star_116_654 (I : Type u) (A : Type v) : SimilarType (FamilyProduct I (fun _ => A)) (I → A) :=
  ⟨equivRefl _⟩

end PM.Architecture.Star116SixthKernel
