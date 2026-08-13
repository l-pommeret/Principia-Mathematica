import Principia.Architecture.Star116ThirdKernel

namespace PM.Architecture.Star116FourthKernel
open Star116SecondKernel Star116ThirdKernel

def FamilyProduct (I : Type u) (F : I → Type v) := (i : I) → F i

def equivRefl (A : Type u) : TypeEquiv A A := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def equivSymm (e : TypeEquiv A B) : TypeEquiv B A := ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩
def equivTrans (e : TypeEquiv A B) (f : TypeEquiv B C) : TypeEquiv A C :=
  ⟨fun x => f.toFun (e.toFun x), fun z => e.invFun (f.invFun z),
   fun x => by change e.invFun (f.invFun (f.toFun (e.toFun x))) = x; rw [f.leftInv, e.leftInv],
   fun z => by change f.toFun (e.toFun (e.invFun (f.invFun z))) = z; rw [e.rightInv, f.rightInv]⟩

theorem star_116_352 (B : Type u) [Nonempty B] : EmptyType (B → Zero) := star_116_31 B
theorem star_116_353 (B : Type u) [Nonempty B] : EmptyType (B → Zero) ↔ EmptyType Zero := by
  exact star_116_35 Zero B
theorem star_116_36 (h : SimilarType A B) : SimilarType A B := h
theorem star_116_361 (h : SimilarType A B) : CardinalClass A = CardinalClass B := by
  obtain ⟨e⟩ := h
  funext X; apply propext; constructor
  · rintro ⟨f⟩; exact ⟨equivTrans f e⟩
  · rintro ⟨f⟩; exact ⟨equivTrans f (equivSymm e)⟩
theorem star_116_4 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_401 (e : TypeEquiv A B) : e.invFun ∘ e.toFun = id := by funext x; exact e.leftInv x
theorem star_116_41 (e : TypeEquiv A B) : e.toFun ∘ e.invFun = id := by funext x; exact e.rightInv x
theorem star_116_411 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_361 ⟨e⟩
theorem star_116_412 (e : TypeEquiv A B) : SimilarType B A := ⟨equivSymm e⟩
theorem star_116_413 (e : TypeEquiv A B) : e.invFun ∘ e.toFun = id := star_116_401 e
theorem star_116_414 (e : TypeEquiv A B) : SimilarType A B ∧ SimilarType B A := ⟨⟨e⟩, ⟨equivSymm e⟩⟩
theorem star_116_42 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_411 e

def reindexProduct (e : TypeEquiv I J) (A : Type v) :
    TypeEquiv (J → A) (I → A) where
  toFun f i := f (e.toFun i)
  invFun g j := g (e.invFun j)
  leftInv f := funext fun j => by change f (e.toFun (e.invFun j)) = f j; rw [e.rightInv]
  rightInv g := funext fun i => by change g (e.invFun (e.toFun i)) = g i; rw [e.leftInv]

theorem star_116_422 (e : TypeEquiv I J) (A : Type v) :
    SimilarType (J → A) (I → A) := ⟨reindexProduct e A⟩
theorem star_116_43 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_44 (e : TypeEquiv A B) : SimilarType A B := star_116_43 e

end PM.Architecture.Star116FourthKernel
