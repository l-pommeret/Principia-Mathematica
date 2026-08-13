import Principia.Architecture.Star114MiddleKernel

/-! # PM II, ✱114·57–✱114·63: explicit product correlations. -/
namespace PM.Architecture.Star114ClosingKernel
open PM.Architecture.Star114OpeningKernel
open PM.Architecture.Star114MiddleKernel
open PM.Architecture.Star115OpeningKernel
open PM.Architecture.Star115ClosingKernel

def MapGraph {F G : I → Type u} (e : ∀ i, F i → G i)
    (f : CardinalProduct F) (g : CardinalProduct G) := g = ProductMap e f

/-- ✱114·57, the multiplicative principle makes pointwise isomorphism product-invariant. -/
theorem star_114_57 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : ProductExists F ↔ ProductExists G := star_114_56 h

/-- ✱114·571, equal cardinal representatives have equal product-existence values. -/
theorem star_114_571 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : ProductExists F ↔ ProductExists G := star_114_57 h

/-- ✱114·6, products indexed by corresponding disjoint families agree. -/
theorem star_114_6 {F : I → Type u} (p : J → I) (q : I → J)
    (hp : ∀ i, p (q i) = i) (hq : ∀ j, q (p j) = j) :
    ProductExists F ↔ ProductExists (fun j => F (p j)) := star_114_52 p q hp hq

/-- ✱114·601, a family of component maps induces a product map. -/
theorem star_114_601 {F G : I → Type u} (e : ∀ i, F i → G i) :
    ∀ f : CardinalProduct F, ∃ g : CardinalProduct G, MapGraph e f g :=
  fun f => ⟨ProductMap e f, rfl⟩

/-- ✱114·602, the graph of an induced product map is functional and total. -/
theorem star_114_602 {F G : I → Type u} (e : ∀ i, F i → G i) :
    (∀ f, ∃ g, MapGraph e f g) ∧
      (∀ ⦃f : CardinalProduct F⦄ ⦃g h : CardinalProduct G⦄,
        MapGraph e f g → MapGraph e f h → g = h) := by
  exact ⟨star_114_601 e, fun {_} {_ _} h₁ h₂ => h₁.trans h₂.symm⟩

/-- ✱114·603, componentwise graph membership is product-map membership. -/
theorem star_114_603 {F G : I → Type u} (e : ∀ i, F i → G i)
    (f : CardinalProduct F) (g : CardinalProduct G) :
    MapGraph e f g ↔ ∀ i, g i = e i (f i) := by
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- ✱114·604, the assembled correlation is precisely the map graph. -/
theorem star_114_604 {F G : I → Type u} (e : ∀ i, F i → G i) :
    ∀ f g, MapGraph e f g ↔ g = ProductMap e f := fun _ _ => Iff.rfl

/-- ✱114·605, the assembled product correlation is single-valued. -/
theorem star_114_605 {F G : I → Type u} (e : ∀ i, F i → G i) :
    ∀ ⦃f : CardinalProduct F⦄ ⦃g h : CardinalProduct G⦄,
      MapGraph e f g → MapGraph e f h → g = h :=
  fun {_} {_ _} h₁ h₂ => h₁.trans h₂.symm

/-- ✱114·61, every graph value decomposes into its component values. -/
theorem star_114_61 {F G : I → Type u} {e : ∀ i, F i → G i}
    {f : CardinalProduct F} {g : CardinalProduct G} (h : MapGraph e f g) :
    ∀ i, g i = e i (f i) := fun i => congrFun h i

/-- ✱114·611, coordinate restriction of a graph value is the component map. -/
theorem star_114_611 {F G : I → Type u} {e : ∀ i, F i → G i}
    {f : CardinalProduct F} {g : CardinalProduct G} (h : MapGraph e f g) (i : I) :
    g i = e i (f i) := star_114_61 h i

/-- ✱114·612, component equations reconstruct the product graph. -/
theorem star_114_612 {F G : I → Type u} {e : ∀ i, F i → G i}
    {f : CardinalProduct F} {g : CardinalProduct G}
    (h : ∀ i, g i = e i (f i)) : MapGraph e f g := funext h

/-- ✱114·613, reconstruction followed by decomposition is identity. -/
theorem star_114_613 {F G : I → Type u} {e : ∀ i, F i → G i}
    {f : CardinalProduct F} {g : CardinalProduct G}
    (h : ∀ i, g i = e i (f i)) : ∀ i, g i = e i (f i) :=
  star_114_61 (star_114_612 h)

/-- ✱114·614, every source product element lies in the graph domain. -/
theorem star_114_614 {F G : I → Type u} (e : ∀ i, F i → G i) (f : CardinalProduct F) :
    ∃ g, MapGraph e f g := star_114_601 e f

/-- ✱114·62, pointwise isomorphisms induce a one-one onto product correlation. -/
theorem star_114_62 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) :
    Function.Injective (ProductMap e) ∧ Function.Surjective (ProductMap e) := star_115_51 h

/-- ✱114·621, a pointwise isomorphism therefore preserves product existence. -/
theorem star_114_621 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : ProductExists F ↔ ProductExists G := star_114_57 h

/-- ✱114·63, the explicit product correlation exists whenever component maps do. -/
theorem star_114_63 {F G : I → Type u} (e : ∀ i, F i → G i) :
    ∀ f : CardinalProduct F, UniqueValue (MapGraph e f) :=
  fun f => ⟨ProductMap e f, rfl, fun _ h => h⟩

end PM.Architecture.Star114ClosingKernel
