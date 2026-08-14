import Principia.Architecture.Star116FourthKernel

namespace PM.Architecture.Star116FifthKernel
open Star116SecondKernel Star116FourthKernel

def sumExpEquiv (A : Type u) (B : Type v) (C : Type w) :
    TypeEquiv ((B → A) × (C → A)) (Sum B C → A) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun b => f (Sum.inl b), fun c => f (Sum.inr c))
  leftInv p := by cases p; rfl
  rightInv f := funext fun x => by cases x <;> rfl

def prodExpEquiv (A : Type u) (B : Type v) (C : Type w) :
    TypeEquiv ((C → A) × (C → B)) (C → A × B) where
  toFun p c := (p.1 c, p.2 c)
  invFun f := (fun c => (f c).1, fun c => (f c).2)
  leftInv p := by cases p; rfl
  rightInv f := funext fun c => Prod.eta (f c)

def curryEquiv (A : Type u) (B : Type v) (C : Type w) :
    TypeEquiv (B × C → A) (C → B → A) where
  toFun f c b := f (b,c)
  invFun f p := f p.2 p.1
  leftInv f := funext fun p => by cases p; rfl
  rightInv f := rfl

theorem star_116_45 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_5 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((B → A) × (C → A)) (Sum B C → A) := ⟨sumExpEquiv A B C⟩
theorem star_116_51 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((B → A) × (C → A)) (Sum B C → A) := star_116_5 A B C
theorem star_116_52 (A : Type u) (B : Type v) (C : Type w) :
    Star116SecondKernel.CardinalClass ((B → A) × (C → A)) =
      Star116SecondKernel.CardinalClass (Sum B C → A) :=
  star_116_361 (star_116_51 A B C)
theorem star_116_529 (e : TypeEquiv A B) : SimilarType B A := ⟨equivSymm e⟩
theorem star_116_53 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((C → A) × (C → B)) (C → A × B) := ⟨prodExpEquiv A B C⟩
theorem star_116_531 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((C → A) × (C → B)) (C → A × B) := ⟨prodExpEquiv A B C⟩
theorem star_116_532 (A : Type u) (B : Type v) (C : Type w) :
    (prodExpEquiv A B C).invFun ∘ (prodExpEquiv A B C).toFun = id := by
  funext x; exact (prodExpEquiv A B C).leftInv x
theorem star_116_533 (A : Type u) (B : Type v) (C : Type w) :
    (prodExpEquiv A B C).toFun ∘ (prodExpEquiv A B C).invFun = id := by
  funext x; exact (prodExpEquiv A B C).rightInv x
theorem star_116_534 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((C → A) × (C → B)) (C → A × B) := star_116_53 A B C
theorem star_116_535 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (C → A × B) ((C → A) × (C → B)) := ⟨equivSymm (prodExpEquiv A B C)⟩
theorem star_116_54 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType ((C → A) × (C → B)) (C → A × B) := star_116_53 A B C
theorem star_116_55 (A : Type u) (B : Type v) (C : Type w) :
    Star116SecondKernel.CardinalClass ((C → A) × (C → B)) =
      Star116SecondKernel.CardinalClass (C → A × B) :=
  star_116_361 (star_116_54 A B C)
theorem star_116_6 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := ⟨curryEquiv A B C⟩
theorem star_116_601 (A : Type u) (B : Type v) (C : Type w) :
    (curryEquiv A B C).invFun ∘ (curryEquiv A B C).toFun = id := by
  funext f; exact (curryEquiv A B C).leftInv f

end PM.Architecture.Star116FifthKernel
