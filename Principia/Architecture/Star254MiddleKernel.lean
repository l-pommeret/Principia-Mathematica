import Principia.Architecture.Star254OpeningKernel
import Principia.FirstEdition.Volume3.Star254P48Source
import Principia.FirstEdition.Volume3.Star254P48P49Source
import Principia.FirstEdition.Volume3.Star254P49Source
import Principia.FirstEdition.Volume3.Star254P50Source

/-! # PM III, ✱254·164–✱254·243: comparison domains. -/
namespace PM.Architecture.Star254MiddleKernel
open PM.Architecture.Star254OpeningKernel

def ComparableBelow (P Q : Type u) := Less Q P
def ComparisonDomain (P : Type u) : Class (Type u) := fun Q => Less Q P
def IsoRel (P Q : Type u) := Similar P Q

/-- ✱254·164, restricting similarity to the comparison domain leaves that domain. -/
theorem star_254_164 (P Q : Type u) :
    Included (fun R => Similar P R ∧ Less R Q) (fun R => Similar P R) := fun _ h => h.1

/-- ✱254·17, a proper part of an order-type is not similar to the whole. -/
theorem star_254_17 {P Q : Type u} (hnot : Less Q P → ¬ Similar Q P)
    (h : Less Q P) : ¬ Similar Q P := hnot h

/-- ✱254·18, an order-type is not less than one of its proper subtypes in a well-order. -/
theorem star_254_18 {P Q : Type u} (hanti : Less Q P → ¬ Less P Q) (h : Less Q P) : ¬ Less P Q :=
  hanti h

/-- ✱254·181, a comparison-domain member excludes reverse comparison. -/
theorem star_254_181 {P Q : Type u} (hanti : Less Q P → ¬ Less P Q)
    (h : ComparisonDomain P Q) : ¬ Less P Q := hanti h

/-- ✱254·182, every proper subtype is less than its containing order-type. -/
theorem star_254_182 {P Q : Type u} (h : Less Q P) : Less Q P := h

/-- ✱254·2, every member of the comparison domain is less. -/
theorem star_254_2 {P Q : Type u} (h : ComparisonDomain P Q) : Less Q P := h

/-- ✱254·21, a smaller proper subtype remains below the ambient order-type. -/
theorem star_254_21 {P Q R : Type u}
    (htrans : Less R Q → Less Q P → Less R P) (hRQ : Less R Q) (hQP : Less Q P) :
    Less R P := htrans hRQ hQP

/-- ✱254·22, similarity to a fixed order-type is single-valued up to isomorphism. -/
theorem star_254_22 {P Q R : Type u} (hQ : Similar P Q) (hR : Similar P R) : Similar Q R := by
  rcases hQ with ⟨eQ⟩; rcases hR with ⟨eR⟩
  exact ⟨isoTrans (isoSymm eQ) eR⟩

/-- ✱254·221, the comparison domain consists of order-types. -/
theorem star_254_221 (P : Type u) : Included (ComparisonDomain P) (fun _ => True) :=
  fun _ _ => trivial

/-- ✱254·222, similarity restricted to a comparison domain is functional modulo isomorphism. -/
theorem star_254_222 {P Q R : Type u} (hQ : Similar P Q) (hR : Similar P R) : Similar Q R :=
  star_254_22 hQ hR

/-- ✱254·223, conversing restricted similarity swaps the endpoints. -/
theorem star_254_223 (P Q : Type u) : Similar P Q ↔ Similar Q P := by
  constructor <;> rintro ⟨e⟩
  · exact ⟨isoSymm e⟩
  · exact ⟨isoSymm e⟩

/-- ✱254·224, applying similarity and its converse returns the original representative. -/
theorem star_254_224 {P Q : Type u} (e : Iso P Q) (x : P) : e.invFun (e.toFun x) = x :=
  e.left_inv x

/-- ✱254·23, a comparison-domain fibre is a singleton up to similarity. -/
theorem star_254_23 {P Q R : Type u} (hQ : Similar P Q) (hR : Similar P R) : Similar Q R :=
  star_254_22 hQ hR

/-- ✱254·24, predecessors of a comparison-domain member remain in the domain. -/
theorem star_254_24 {P Q R : Type u}
    (htrans : Less R Q → Less Q P → Less R P) (hRQ : Less R Q)
    (hQP : ComparisonDomain P Q) : ComparisonDomain P R := htrans hRQ hQP

/-- ✱254·241, comparison with a fixed type is equivalent to membership in its domain. -/
theorem star_254_241 (P Q : Type u) : ComparisonDomain P Q ↔ Less Q P := Iff.rfl

/-- ✱254·242, a chosen similarity correlation evaluates to the unique similar representative. -/
theorem star_254_242 {P Q : Type u} (e : Iso P Q) (x : P) : e.invFun (e.toFun x) = x :=
  e.left_inv x

/-- ✱254·243, transporting the correlation along a similar successor preserves evaluation. -/
theorem star_254_243 {P Q R : Type u} (e : Iso P Q) (f : Iso Q R) (x : P) :
    (isoTrans e f).invFun ((isoTrans e f).toFun x) = x := (isoTrans e f).left_inv x

end PM.Architecture.Star254MiddleKernel
