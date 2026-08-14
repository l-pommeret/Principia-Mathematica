/-! # PM II, ✱115 opening source ledger

Project Gutenberg ebook 78255, section ✱115, “The product of a class of
cardinal numbers”; opening loci transcribed from the HTML edition.
-/
/- PM-VERBATIM-BEGIN PM2:✱115·01
✱115·01. Prodʻκ = Dʻʻ∈_Δʻκ Df
PM-VERBATIM-END PM2:✱115·01 -/
/- PM-VERBATIM-BEGIN PM2:✱115·02
✱115·02. Cls³ arithm = κ̂(κ,sʻκ ∈ Cls² excl) Df
PM-VERBATIM-END PM2:✱115·02 -/
/- PM-VERBATIM-BEGIN PM2:✱115·1
✱115·1. ⊢ . Prodʻκ = Dʻʻ∈_Δʻκ [(✱115·01)]
PM-VERBATIM-END PM2:✱115·1 -/
/- PM-VERBATIM-BEGIN PM2:✱115·101
✱115·101. ⊢ :: α∈κ .⊃_α. ϖ∩α∈1 : ϖ⊆sʻκ :⊃. ϖ∈Prodʻκ [✱84·411]
PM-VERBATIM-END PM2:✱115·101 -/
/- PM-VERBATIM-BEGIN PM2:✱115·11
✱115·11. ⊢ :: κ∈Cls² excl .⊃: ϖ∈Prodʻκ .≡: α∈κ .⊃_α. ϖ∩α∈1 : ϖ⊆sʻκ [✱84·412]
PM-VERBATIM-END PM2:✱115·11 -/
namespace PM.FirstEdition.Volume2.Star115Source
def gutenbergId : Nat := 78255
def openingLoci : List String :=
  ["115·01", "115·02", "115·1", "115·101", "115·11", "115·12", "115·13",
   "115·131", "115·14", "115·141", "115·142", "115·143", "115·144",
   "115·145", "115·15", "115·151", "115·152", "115·153"]
def sourceSummary : String :=
  "Prod'κ=D''∈Δ'κ; choice classes, binary products, disjoint unions, singleton families, evaluation relations and product similarity."
end PM.FirstEdition.Volume2.Star115Source
