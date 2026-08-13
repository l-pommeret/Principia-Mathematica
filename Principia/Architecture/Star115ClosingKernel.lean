import Principia.Architecture.Star115MiddleKernel

/-! # PM II, ✱115·35–✱115·63: iterated products and invariance. -/
namespace PM.Architecture.Star115ClosingKernel
open PM.Architecture.Star115OpeningKernel

def ProductMap {F G : I → Type u} (e : ∀ i, F i → G i) (f : ClassProduct F) : ClassProduct G :=
  fun i => e i (f i)
def PointwiseIso {F G : I → Type u} (e : ∀ i, F i → G i) (r : ∀ i, G i → F i) :=
  (∀ i x, r i (e i x) = x) ∧ ∀ i y, e i (r i y) = y

/-- ✱115·35, an arithmetical family has a product element. -/
theorem star_115_35 {F : I → Type u} (h : ArithmeticFamily F) : Nonempty (ClassProduct F) :=
  star_115_145 F h

/-- ✱115·4, a pointwise map acts on products pointwise. -/
theorem star_115_4 {F G : I → Type u} (e : ∀ i, F i → G i) (f : ClassProduct F) (i : I) :
    ProductMap e f i = e i (f i) := rfl

/-- ✱115·41, pointwise injectivity makes the product map injective. -/
theorem star_115_41 {F G : I → Type u} {e : ∀ i, F i → G i}
    (he : ∀ i ⦃x y⦄, e i x = e i y → x = y) : Function.Injective (ProductMap e) := by
  intro f g h; funext i; exact he i (congrFun h i)

/-- ✱115·42, a product of products is the corresponding doubly indexed product. -/
theorem star_115_42 {I J : Type v} (F : I → J → Type u) :
    ClassProduct (fun i => ClassProduct (F i)) = ((i : I) → (j : J) → F i j) := rfl

/-- ✱115·43, currying identifies a product over pairs with an iterated product. -/
theorem star_115_43 {I J : Type v} (F : I → J → Type u) :
    Nonempty (ClassProduct (fun p : I × J => F p.1 p.2)) ↔
      Nonempty (ClassProduct (fun i => ClassProduct (F i))) := by
  exact ⟨fun ⟨f⟩ => ⟨fun i j => f (i, j)⟩, fun ⟨f⟩ => ⟨fun p => f p.1 p.2⟩⟩

/-- ✱115·44, flattening and currying iterated products are inverse. -/
theorem star_115_44 {I J : Type v} (F : I → J → Type u)
    (f : ClassProduct (fun i => ClassProduct (F i))) :
    (fun i j => (fun p : I × J => f p.1 p.2) (i, j)) = f := rfl

/-- ✱115·45, distinct outer indices keep their evaluation fibres distinct. -/
theorem star_115_45 {I J : Type v} {F : I → J → Type u}
    {f g : ClassProduct (fun i => ClassProduct (F i))}
    (h : ∀ i j, f i j = g i j) : f = g := by funext i j; exact h i j

/-- ✱115·46, flattening an iterated product is injective. -/
theorem star_115_46 {I J : Type v} (F : I → J → Type u) :
    Function.Injective (fun f : ClassProduct (fun i => ClassProduct (F i)) =>
      fun p : I × J => f p.1 p.2) := by
  intro f g h; funext i j; exact congrFun h (i, j)

/-- ✱115·5, pointwise inverse maps induce inverse product maps. -/
theorem star_115_5 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) (f : ClassProduct F) : ProductMap r (ProductMap e f) = f := by
  funext i; exact h.1 i (f i)

/-- ✱115·501, the induced product map is injective. -/
theorem star_115_501 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : Function.Injective (ProductMap e) := by
  intro f g q
  have := congrArg (ProductMap r) q
  simpa [star_115_5 h f, star_115_5 h g] using this

/-- ✱115·502, the induced product map is surjective. -/
theorem star_115_502 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : Function.Surjective (ProductMap e) := by
  intro g; refine ⟨ProductMap r g, ?_⟩
  funext i; exact h.2 i (g i)

/-- ✱115·51, pointwise isomorphic families have bijective products. -/
theorem star_115_51 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) :
    Function.Injective (ProductMap e) ∧ Function.Surjective (ProductMap e) :=
  ⟨star_115_501 h, star_115_502 h⟩

/-- ✱115·6, two indexed image families give corresponding product images. -/
theorem star_115_6 {F G : I → Type u} (e : ∀ i, F i → G i) (f : ClassProduct F) :
    ∃ g : ClassProduct G, g = ProductMap e f := ⟨ProductMap e f, rfl⟩

/-- ✱115·601, equality of pointwise maps gives equality of product maps. -/
theorem star_115_601 {F G : I → Type u} {e d : ∀ i, F i → G i}
    (h : ∀ i x, e i x = d i x) : ProductMap e = ProductMap d := by
  funext f i; exact h i (f i)

/-- ✱115·602, composition of pointwise maps commutes with product formation. -/
theorem star_115_602 {F G H : I → Type u} (e : ∀ i, F i → G i)
    (d : ∀ i, G i → H i) (f : ClassProduct F) :
    ProductMap d (ProductMap e f) = ProductMap (fun i x => d i (e i x)) f := rfl

/-- ✱115·61, injective pointwise maps preserve equality of product elements. -/
theorem star_115_61 {F G : I → Type u} {e : ∀ i, F i → G i}
    (h : ∀ i, Function.Injective (e i)) {f g : ClassProduct F} :
    ProductMap e f = ProductMap e g → f = g := fun q => star_115_41 h q

/-- ✱115·62, pointwise surjections make the product map surjective. -/
theorem star_115_62 {F G : I → Type u} {e : ∀ i, F i → G i}
    (h : ∀ i, Function.Surjective (e i)) : Function.Surjective (ProductMap e) := by
  classical
  intro g
  let f : ClassProduct F := fun i => Classical.choose (h i (g i))
  refine ⟨f, ?_⟩
  funext i; exact Classical.choose_spec (h i (g i))

/-- ✱115·63, pointwise bijections induce a bijection on products. -/
theorem star_115_63 {F G : I → Type u} {e : ∀ i, F i → G i}
    (hi : ∀ i, Function.Injective (e i)) (hs : ∀ i, Function.Surjective (e i)) :
    Function.Injective (ProductMap e) ∧ Function.Surjective (ProductMap e) :=
  ⟨star_115_41 hi, star_115_62 hs⟩

end PM.Architecture.Star115ClosingKernel
