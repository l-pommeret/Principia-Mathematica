import Principia.Architecture.Star114OpeningKernel
import Principia.Architecture.Star115ClosingKernel

/-! # PM II, ✱114·33–✱114·562: product invariance and transport. -/
namespace PM.Architecture.Star114MiddleKernel
open PM.Architecture.Star114OpeningKernel
open PM.Architecture.Star115OpeningKernel
open PM.Architecture.Star115ClosingKernel

/-- ✱114·33, adjoining a new factor multiplies the product. -/
theorem star_114_33 (F : I → Type u) (A : Type u) :
    ProductExists (fun x : Sum I Unit => Sum.casesOn x F (fun _ => A)) ↔
      Nonempty (CardinalProduct F × A) := by
  constructor
  · rintro ⟨f⟩; exact ⟨(fun i => f (.inl i)), f (.inr ())⟩
  · rintro ⟨f, a⟩; exact ⟨fun x => Sum.casesOn x f (fun _ => a)⟩

/-- ✱114·34, the enlarged product is non-null exactly when both parts are. -/
theorem star_114_34 (F : I → Type u) (A : Type u) :
    ProductExists (fun x : Sum I Unit => Sum.casesOn x F (fun _ => A)) ↔
      ProductExists F ∧ Nonempty A := by
  rw [star_114_3]
  exact and_congr Iff.rfl (star_114_21 A)

/-- ✱114·35, the product of two distinct singleton-indexed factors is binary product. -/
theorem star_114_35 (A B : Type u) :
    ProductExists (fun i : Bool => if i then A else B) ↔ Nonempty (A × B) :=
  star_115_13 A B

/-- ✱114·36, adjoining an inhabited factor preserves product existence. -/
theorem star_114_36 (F : I → Type u) (A : Type u) (hA : Nonempty A) :
    ProductExists (fun x : Sum I Unit => Sum.casesOn x F (fun _ => A)) ↔ ProductExists F := by
  rw [star_114_34]
  simp [hA]

/-- ✱114·4, a pointwise injection acts functorially on cardinal products. -/
theorem star_114_4 {F G : I → Type u} (e : ∀ i, F i → G i) (f : CardinalProduct F) :
    ∃ g : CardinalProduct G, g = ProductMap e f := ⟨ProductMap e f, rfl⟩

/-- ✱114·41, adjoining only singleton factors does not change non-nullity. -/
theorem star_114_41 {I J : Type v} {A : Type u} (F : I → Type u) (a : J → A) :
    ProductExists (fun x : Sum I J => Sum.casesOn x F (fun j => {y : A // y = a j})) ↔
      ProductExists F := by
  rw [star_114_3]
  have hs : ProductExists (fun j => {y : A // y = a j}) :=
    ⟨fun j => ⟨a j, rfl⟩⟩
  simp [hs]

/-- ✱114·42, deleting singleton factors leaves the same existence value. -/
theorem star_114_42 {I J : Type v} {A : Type u} (F : I → Type u) (a : J → A) :
    ProductExists (fun x : Sum I J => Sum.casesOn x F (fun j => {y : A // y = a j})) ↔
      ProductExists F := star_114_41 F a

/-- ✱114·43, a singleton extension of a product has a canonical restriction. -/
theorem star_114_43 {I J : Type v} {A : Type u} {F : I → Type u} {a : J → A}
    (h : ProductExists (fun x : Sum I J => Sum.casesOn x F (fun j => {y : A // y = a j}))) :
    ProductExists F := (star_114_41 F a).mp h

/-- ✱114·5, pointwise inverse maps transport cardinal products. -/
theorem star_114_5 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) (f : CardinalProduct F) : ProductMap r (ProductMap e f) = f :=
  star_115_5 h f

/-- ✱114·501, restriction of a pointwise transport determines the same product map. -/
theorem star_114_501 {F G : I → Type u} {e d : ∀ i, F i → G i}
    (h : ∀ i x, e i x = d i x) : ProductMap e = ProductMap d := star_115_601 h

/-- ✱114·51, isomorphic factor families have bijective products. -/
theorem star_114_51 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) :
    Function.Injective (ProductMap e) ∧ Function.Surjective (ProductMap e) := star_115_51 h

/-- ✱114·52, reindexing along a bijection preserves product existence. -/
theorem star_114_52 {F : I → Type u} (p : J → I) (q : I → J)
    (hp : ∀ i, p (q i) = i) (_hq : ∀ j, q (p j) = j) :
    ProductExists F ↔ ProductExists (fun j => F (p j)) := by
  constructor
  · exact fun h => star_114_24 h p
  · rintro ⟨g⟩
    exact ⟨fun i => cast (congrArg F (hp i)) (g (q i))⟩

/-- ✱114·53, identity reindexing fixes the product. -/
theorem star_114_53 (F : I → Type u) :
    ProductExists F ↔ ProductExists (fun i => F i) := Iff.rfl

/-- ✱114·54, composition of reindexings composes product restrictions. -/
theorem star_114_54 {F : I → Type u} (p : J → I) (q : K → J) (f : CardinalProduct F) :
    (fun k => f (p (q k))) = (fun k => (fun j => f (p j)) (q k)) := rfl

/-- ✱114·56, a factorwise isomorphism preserves product existence. -/
theorem star_114_56 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (_h : PointwiseIso e r) : ProductExists F ↔ ProductExists G := by
  constructor
  · rintro ⟨f⟩; exact ⟨ProductMap e f⟩
  · rintro ⟨g⟩; exact ⟨ProductMap r g⟩

/-- ✱114·561, the induced product transport is one-one. -/
theorem star_114_561 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : Function.Injective (ProductMap e) := star_115_501 h

/-- ✱114·562, the induced product transport is onto. -/
theorem star_114_562 {F G : I → Type u} {e : ∀ i, F i → G i} {r : ∀ i, G i → F i}
    (h : PointwiseIso e r) : Function.Surjective (ProductMap e) := star_115_502 h

end PM.Architecture.Star114MiddleKernel
