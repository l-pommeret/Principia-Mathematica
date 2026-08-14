/-! # PM II, ✱114 source ledger

Project Gutenberg ebook 78255, section ✱114, cardinal products.
-/

/- PM-VERBATIM-BEGIN PM2:✱114·01
✱114·01. ΠNcʻκ = Ncʻ∈Δʻκ Df
PM-VERBATIM-END PM2:✱114·01 -/

/- PM-VERBATIM-BEGIN PM2:✱114·1
✱114·1. ⊢ . ΠNcʻκ = Ncʻ∈Δʻκ [(✱114·01)]
PM-VERBATIM-END PM2:✱114·1 -/

/- PM-VERBATIM-BEGIN PM2:✱114·11
✱114·11. ⊢ : β∈ΠNcʻκ .≡. β sm ∈Δʻκ .≡. β∈Ncʻ∈Δʻκ [✱114·1.✱100·31]
PM-VERBATIM-END PM2:✱114·11 -/

/- PM-VERBATIM-BEGIN PM2:✱114·12
✱114·12. ⊢ . ∈Δʻκ∈ΠNcʻκ [✱100·3.✱114·1]
PM-VERBATIM-END PM2:✱114·12 -/

/- PM-VERBATIM-BEGIN PM2:✱114·2
✱114·2. ⊢ . ΠNcʻΛ = 1 [✱83·15.✱101·2]
PM-VERBATIM-END PM2:✱114·2 -/

namespace PM.FirstEdition.Volume2.Star114Source
def gutenbergId : Nat := 78255
def openingLoci : List String :=
  ["114·01", "114·1", "114·11", "114·12", "114·2", "114·21", "114·22",
   "114·23", "114·24", "114·25", "114·26", "114·261", "114·27", "114·3",
   "114·301", "114·31", "114·311", "114·32"]
def sourceSummary : String :=
  "Definition and elementary laws of ΠNc, null factors, the multiplicative principle, and products over unions."
end PM.FirstEdition.Volume2.Star114Source
