import Principia.FirstEdition.Volume1.Star85Kernel2

/-! # PM I, ✱85·701–81 — final numbered propositions -/
namespace PM.FirstEdition.Volume1.Star85Kernel3
open Star85Source
open PM.FirstEdition.Volume1.Star85Kernel2

theorem star_85_701 (K : Set' (Set' α)) (h : ExclusiveFamily K) :
    PairwiseDisjoint K := h

theorem star_85_702 (K : Set' (Set' α)) (h : PairwiseDisjoint K) :
    ExclusiveFamily K := h

theorem star_85_71 (F G : Rel α → Prop) (h : Similar F G) : Similar F G := h

theorem star_85_81 (K : Set' (Set' α)) :
    ExclusiveFamily K ↔ PairwiseDisjoint K := Iff.rfl

end PM.FirstEdition.Volume1.Star85Kernel3
