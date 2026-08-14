/-!
# Principia Mathematica I, ✱95 — equi-factor relation

Canonical witness: Project Gutenberg ebook 78050 and the 1910 Volume I
facsimile, printed page 627 (scan leaf 649).
-/

/- PM-VERBATIM-BEGIN PM1:✱95·01
✱95·01. (P∗Q) = sgʻ{(P∥Q)∗} Dft [✱95]
PM-VERBATIM-END PM1:✱95·01 -/
/- PM-VERBATIM-BEGIN PM1:✱95·1
✱95·1. ⊢ :: M∈(P∗Q)ʻR .≡: R∈μ : N∈μ .⊃_N. P|N|Q∈μ :⊃_μ. M∈μ
PM-VERBATIM-END PM1:✱95·1 -/
/- PM-VERBATIM-BEGIN PM1:✱95·11
✱95·11. ⊢ : φR : φN .⊃_N. φ(P|N|Q) :⊃: M∈(P∗Q)ʻR .⊃_M. φM
PM-VERBATIM-END PM1:✱95·11 -/
/- PM-VERBATIM-BEGIN PM1:✱95·12
✱95·12. ⊢ : M∈(P∗Q)ʻR .⊃_M. φ(P|M|Q) :⊃: N∈(P∗Q)ʻR−ιʻR .⊃_N. φN
PM-VERBATIM-END PM1:✱95·12 -/
/- PM-VERBATIM-BEGIN PM1:✱95·13
✱95·13. ⊢ . R∈(P∗Q)ʻR [✱95·1]
PM-VERBATIM-END PM1:✱95·13 -/
/- PM-VERBATIM-BEGIN PM1:✱95·131
✱95·131. ⊢ . P|R|Q∈(P∗Q)ʻR
PM-VERBATIM-END PM1:✱95·131 -/
/- PM-VERBATIM-BEGIN PM1:✱95·132
✱95·132. ⊢ : M∈(P∗Q)ʻR .⊃. P|M|Q∈(P∗Q)ʻR
PM-VERBATIM-END PM1:✱95·132 -/
/- PM-VERBATIM-BEGIN PM1:✱95·14
✱95·14. ⊢ : φR : N∈(P∗Q)ʻR . φN .⊃_N. φ(P|N|Q) :⊃: M∈(P∗Q)ʻR .⊃_M. φM
PM-VERBATIM-END PM1:✱95·14 -/
/- PM-VERBATIM-BEGIN PM1:✱95·21
✱95·21. ⊢ : M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotʻP∪ιʻI . T∈PotʻQ∪ιʻI . M=S|R|T
PM-VERBATIM-END PM1:✱95·21 -/
/- PM-VERBATIM-BEGIN PM1:✱95·211
✱95·211. ⊢ : ᗡʻR⊂CʻQ . M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotʻP∪ιʻI . T∈PotidʻQ . M=S|R|T
PM-VERBATIM-END PM1:✱95·211 -/

namespace PM.FirstEdition.Volume1.Star95Source

abbrev Rel (α : Sort u) := α → α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z

/-- ✱95·01: the least class containing `R` and closed under `M ↦ P|M|Q`. -/
inductive Equi (P Q R : Rel α) : Rel α → Prop
  | base : Equi P Q R R
  | step {M} : Equi P Q R M → Equi P Q R (comp (comp P M) Q)

end PM.FirstEdition.Volume1.Star95Source
