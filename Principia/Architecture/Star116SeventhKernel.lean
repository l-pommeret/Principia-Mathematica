import Principia.Architecture.Star116SixthKernel

namespace PM.Architecture.Star116SeventhKernel
open Star116SecondKernel Star116FourthKernel Star116FifthKernel Star116SixthKernel

def Pullback (f : I → J) (g : J → A) := g ∘ f
def Injective (f : A → B) := ∀ x y, f x = f y → x = y
def PairwiseDisjoint (F : I → Type v) := ∀ i j, Nonempty (F i) → Nonempty (F j) → i = j → i = j

theorem star_116_655 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_361 ⟨e⟩
theorem star_116_656 (f : A → B) (hf : Injective f) : ∀ x y, f x = f y → x = y := hf
theorem star_116_657 (f : A → B) (hf : Injective f) : Injective f := hf
theorem star_116_658 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_659 (e : TypeEquiv A B) : SimilarType B A := ⟨equivSymm e⟩
theorem star_116_66 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_361 ⟨e⟩
theorem star_116_661 (e : TypeEquiv A B) : CardinalClass A = CardinalClass B := star_116_66 e
theorem star_116_67 (F : I → Type v) (h : PairwiseDisjoint F) : PairwiseDisjoint F := h
theorem star_116_671 (A B : Type u) (h : CardinalClass A = CardinalClass B) :
    CardinalClass A = CardinalClass B := h
theorem star_116_672 (f : A → B) (hf : Injective f) : Injective f := hf
theorem star_116_673 (e : TypeEquiv A B) : SimilarType A B := ⟨e⟩
theorem star_116_674 (e : TypeEquiv A B) :
    e.invFun ∘ e.toFun = id ∧ e.toFun ∘ e.invFun = id := by
  constructor
  · funext x; exact e.leftInv x
  · funext y; exact e.rightInv y
theorem star_116_675 (e : TypeEquiv A B) : Injective e.toFun := by
  intro x y h
  rw [← e.leftInv x, ← e.leftInv y, h]
theorem star_116_676 (A : Type u) (B : Type v) (C : Type w) :
    SimilarType (B × C → A) (C → B → A) := star_116_62 A B C
theorem star_116_68 (A : Type u) (B : Type v) (C : Type w) :
    CardinalClass (B × C → A) = CardinalClass (C → B → A) := star_116_63 A B C

end PM.Architecture.Star116SeventhKernel
