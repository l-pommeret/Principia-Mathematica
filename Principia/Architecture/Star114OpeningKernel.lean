import Principia.Architecture.Star115OpeningKernel
import Principia.FirstEdition.Volume2.Star114Source

/-! # PM II, ✱114·01–✱114·32: cardinal products. -/
namespace PM.Architecture.Star114OpeningKernel
open PM.Architecture.Star115OpeningKernel

def CardinalProduct (F : I → Type u) := ClassProduct F
def ProductExists (F : I → Type u) := Nonempty (CardinalProduct F)
def EmptyType (A : Sort u) := A → False

/-- ✱114·01. `ΠNcʻκ = Ncʻ∈Δʻκ Df`. -/
def star_114_01 (F : I → Type u) : Sort _ := ClassProduct F

/-- ✱114·1, the defining identity. -/
theorem star_114_1 (F : I → Type u) : CardinalProduct F = ((i : I) → F i) := rfl

/-- ✱114·11, membership in a cardinal product is pointwise choice. -/
theorem star_114_11 (F : I → Type u) (f : CardinalProduct F) : ∀ i, Nonempty (F i) :=
  fun i => ⟨f i⟩

/-- ✱114·12, the indexed family itself supplies its canonical product witness. -/
theorem star_114_12 (F : I → Type u) (f : CardinalProduct F) : ProductExists F := ⟨f⟩

/-- ✱114·2, a singleton-indexed cardinal product is its factor. -/
theorem star_114_2 (A : Type u) : ProductExists (fun _ : Unit => A) ↔ Nonempty A :=
  star_115_142 A

/-- ✱114·21, product of the singleton family recovers the factor. -/
theorem star_114_21 (A : Type u) :
    Nonempty (CardinalProduct (fun _ : Unit => A)) ↔ Nonempty A := star_114_2 A

/-- ✱114·22, a singleton family with an empty factor has empty product. -/
theorem star_114_22 : ¬ ProductExists (fun _ : Unit => Empty) := by
  rintro ⟨f⟩; exact f () |>.elim

/-- ✱114·23, any empty factor makes the whole product empty. -/
theorem star_114_23 {ι : Sort v} (F : ι → Type u) (i : ι) (h : EmptyType (F i)) :
    ¬ ProductExists F := by
  rintro ⟨f⟩; exact h (f i)

/-- ✱114·24, existence of a larger product implies existence of every restricted product. -/
theorem star_114_24 {ι : Sort v} {κ : Sort w} {F : ι → Type u}
    (h : ProductExists F) (p : κ → ι) :
    ProductExists (fun j => F (p j)) := by
  rcases h with ⟨f⟩; exact ⟨fun j => f (p j)⟩

/-- ✱114·25, the multiplicative choice principle supplies a product witness. -/
theorem star_114_25 (F : I → Type u) (h : ∀ i, Nonempty (F i)) : ProductExists F := by
  classical
  exact ⟨fun i => Classical.choice (h i)⟩

/-- ✱114·26, a product is empty exactly when some factor is empty. -/
theorem star_114_26 (F : I → Type u) :
    ¬ ProductExists F ↔ ∃ i, EmptyType (F i) := by
  classical
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hnone
    apply hn
    apply star_114_25
    intro i
    apply Classical.byContradiction
    intro hi
    exact hnone ⟨i, fun x => hi ⟨x⟩⟩
  · rintro ⟨i, hi⟩; exact star_114_23 F i hi

/-- ✱114·261, the null cardinal occurs among the factors exactly in the null case. -/
theorem star_114_261 (F : I → Type u) :
    (∃ i, EmptyType (F i)) ↔ ¬ ProductExists F := (star_114_26 F).symm

/-- ✱114·27, a nonempty product has no empty factor. -/
theorem star_114_27 (F : I → Type u) (h : ProductExists F) : ∀ i, Nonempty (F i) := by
  rcases h with ⟨f⟩; exact fun i => ⟨f i⟩

/-- ✱114·3, product over a disjoint union splits. -/
theorem star_114_3 (F : Sum I J → Type u) :
    ProductExists F ↔ ProductExists (fun i => F (.inl i)) ∧
      ProductExists (fun j => F (.inr j)) := by
  constructor
  · rintro ⟨f⟩; exact ⟨⟨fun i => f (.inl i)⟩, ⟨fun j => f (.inr j)⟩⟩
  · rintro ⟨⟨f⟩, ⟨g⟩⟩; exact ⟨fun x => Sum.casesOn x f g⟩

/-- ✱114·301, the tagged union product is the binary product of subproducts. -/
theorem star_114_301 (F : Sum I J → Type u) :
    ProductExists F ↔
      Nonempty (CardinalProduct (fun i => F (.inl i)) ×
        CardinalProduct (fun j => F (.inr j))) := by
  simpa [ProductExists] using star_115_14 F

/-- ✱114·31, multiplication of the two subproducts gives the union product. -/
theorem star_114_31 (F : Sum I J → Type u) :
    ProductExists F ↔ ProductExists (fun i => F (.inl i)) ∧
      ProductExists (fun j => F (.inr j)) := star_114_3 F

/-- ✱114·311, removing overlap before adjoining a second factor leaves the same split. -/
theorem star_114_311 (F : Sum I J → Type u) :
    ProductExists F ↔ ProductExists (fun i => F (.inl i)) ∧
      ProductExists (fun j => F (.inr j)) := star_114_31 F

/-- ✱114·32, a union product is non-null exactly when both subproducts are non-null. -/
theorem star_114_32 (F : Sum I J → Type u) :
    ProductExists F ↔ ProductExists (fun i => F (.inl i)) ∧
      ProductExists (fun j => F (.inr j)) := star_114_31 F

end PM.Architecture.Star114OpeningKernel
