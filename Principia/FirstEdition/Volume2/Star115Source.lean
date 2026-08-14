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
/- PM-VERBATIM-BEGIN PM2:✱115·12
✱115·12. ⊢ : κ∈Cls² excl .⊃. Prodʻκ∈ΠNcʻκ . Prodʻκ sm ∈_Δʻκ [✱84·41]
PM-VERBATIM-END PM2:✱115·12 -/
/- PM-VERBATIM-BEGIN PM2:✱115·13
✱115·13. ⊢ : α∩β=Λ .⊃. Prodʻ(ιʻα∪ιʻβ) sm (α×β) [✱113·152]
PM-VERBATIM-END PM2:✱115·13 -/
/- PM-VERBATIM-BEGIN PM2:✱115·131
✱115·131. ⊢ : α≠β .⊃. Prodʻ(ιʻα∪ιʻβ)=Cʻʻ(α×β) [✱113·151]
PM-VERBATIM-END PM2:✱115·131 -/
/- PM-VERBATIM-BEGIN PM2:✱115·14
✱115·14. ⊢ :: κ∩λ=Λ ∨ sʻκ∩sʻλ=Λ :⊃: ϖ∈Prodʻ(κ∪λ) .≡. (∃ρ,σ). ρ∈Prodʻκ . σ∈Prodʻλ . ϖ=ρ∪σ [✱83·64·641]
PM-VERBATIM-END PM2:✱115·14 -/
/- PM-VERBATIM-BEGIN PM2:✱115·141
✱115·141. ⊢ : ∃!Prodʻκ .⊃. sʻProdʻκ=sʻκ [✱83·66]
PM-VERBATIM-END PM2:✱115·141 -/
/- PM-VERBATIM-BEGIN PM2:✱115·142
✱115·142. ⊢ . Prodʻιʻα=ιʻʻα [✱83·7]
PM-VERBATIM-END PM2:✱115·142 -/
/- PM-VERBATIM-BEGIN PM2:✱115·143
✱115·143. ⊢ . Prodʻιʻʻα=ιʻα [✱83·71]
PM-VERBATIM-END PM2:✱115·143 -/
/- PM-VERBATIM-BEGIN PM2:✱115·144
✱115·144. ⊢ : κ⊆1 .⊃. Prodʻκ=ιʻsʻκ [✱83·72]
PM-VERBATIM-END PM2:✱115·144 -/
/- PM-VERBATIM-BEGIN PM2:✱115·145
✱115·145. ⊢ :: κ∈Cls² excl . α∈κ . μ∩α∈1 .⊃: μ−α∈Prodʻ(κ−ιʻα) .≡. μ∈Prodʻκ [✱84·422]
PM-VERBATIM-END PM2:✱115·145 -/
/- PM-VERBATIM-BEGIN PM2:✱115·15
✱115·15. ⊢ :: κ,λ∈Cls² excl . sʻκ=sʻλ .⊃: κ⊆Prodʻλ .≡. λ⊆Prodʻκ [✱84·43]
PM-VERBATIM-END PM2:✱115·15 -/
/- PM-VERBATIM-BEGIN PM2:✱115·151
✱115·151. ⊢ : κ∈Cls² excl .⊃. ∈_Δʻsʻκ=ṡʻʻProdʻ∈_Δʻʻκ [✱85·28]
PM-VERBATIM-END PM2:✱115·151 -/
/- PM-VERBATIM-BEGIN PM2:✱115·152
✱115·152. ⊢ . P_Δʻα sm ProdʻP↧ʻʻα [✱85·55]
PM-VERBATIM-END PM2:✱115·152 -/
/- PM-VERBATIM-BEGIN PM2:✱115·153
✱115·153. ⊢ . ∈_Δʻκ sm Prodʻ∈↧ʻʻκ [✱115·152]
PM-VERBATIM-END PM2:✱115·153 -/
/- PM-VERBATIM-BEGIN PM2:✱115·154
✱115·154. ⊢ . Prodʻ∈↧ʻʻκ∈ΠNcʻκ [✱115·153]
PM-VERBATIM-END PM2:✱115·154 -/
/- PM-VERBATIM-BEGIN PM2:✱115·16
✱115·16. ⊢ : κ∈Cls² excl .⊃. Prodʻκ⊆Ncʻκ [✱100·64]
PM-VERBATIM-END PM2:✱115·16 -/
namespace PM.FirstEdition.Volume2.Star115Source
def gutenbergId : Nat := 78255
def openingLoci : List String :=
  ["115·01", "115·02", "115·1", "115·101", "115·11", "115·12", "115·13",
   "115·131", "115·14", "115·141", "115·142", "115·143", "115·144",
   "115·145", "115·15", "115·151", "115·152", "115·153"]
def sourceSummary : String :=
  "Prod'κ=D''∈Δ'κ; choice classes, binary products, disjoint unions, singleton families, evaluation relations and product similarity."
end PM.FirstEdition.Volume2.Star115Source
