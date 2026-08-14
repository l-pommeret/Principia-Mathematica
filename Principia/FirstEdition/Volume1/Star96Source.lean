/-!
PM I, ✱96·01–·102. Canonical witness: Project Gutenberg ebook 78050 and
the 1910 Volume I facsimile, printed page 640 (scan leaf 662).
-/

/- PM-VERBATIM-BEGIN PM1:✱96·01
✱96·01. I_Rʻx = R_*⃖ʻx ∩ ẑz(z R_po z) Dft [✱96]
PM-VERBATIM-END PM1:✱96·01 -/
/- PM-VERBATIM-BEGIN PM1:✱96·02
✱96·02. J_Rʻx = R_*⃖ʻx − I_Rʻx Dft [✱96]
PM-VERBATIM-END PM1:✱96·02 -/
/- PM-VERBATIM-BEGIN PM1:✱96·1
✱96·1. ⊢ : z ∈ I_Rʻx .≡. x R_* z . z R_po z
PM-VERBATIM-END PM1:✱96·1 -/
/- PM-VERBATIM-BEGIN PM1:✱96·101
✱96·101. ⊢ : z ∈ J_Rʻx .≡. x R_* z . ∼(z R_po z)
PM-VERBATIM-END PM1:✱96·101 -/
/- PM-VERBATIM-BEGIN PM1:✱96·102
✱96·102. ⊢ . R_*⃖ʻx = J_Rʻx ∪ I_Rʻx . J_Rʻx ∩ I_Rʻx = Λ
PM-VERBATIM-END PM1:✱96·102 -/

namespace PM.FirstEdition.Volume1.Star96Source
def records : List (String × String) := [
  ("✱96·01", "I_Rʻx = R_*⃖ʻx ∩ ẑz(z R_po z)  Dft [✱96]"),
  ("✱96·02", "J_Rʻx = R_*⃖ʻx − I_Rʻx  Dft [✱96]"),
  ("✱96·1", "⊢ : z ∈ I_Rʻx .≡. x R_* z . z R_po z"),
  ("✱96·101", "⊢ : z ∈ J_Rʻx .≡. x R_* z . ∼(z R_po z)"),
  ("✱96·102", "⊢ . R_*⃖ʻx = J_Rʻx ∪ I_Rʻx . J_Rʻx ∩ I_Rʻx = Λ"),
  ("✱96·103", "⊢ . (J_Rʻx)↼hR_po ⊂ J"),
  ("✱96·104", "⊢ : I_Rʻx = Λ .≡. (R_*⃖ʻx)↼hR_po ⊂ J")]
  ++ [
  ("✱96·11", "⊢ . (α↼hR)_po ⊂ α↼hR_po"),
  ("✱96·121", "⊢ : Rʻʻα ⊂ α .⊃. (R↾α)_po = R_po↾α"),
  ("✱96·14", "⊢ : x ∈ CʻR .⊃. R_*⃖ʻx = ιʻx ∪ R_po⃖ʻx")]
end PM.FirstEdition.Volume1.Star96Source
