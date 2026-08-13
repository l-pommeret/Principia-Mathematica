/-! PM III ✱215 opening, Stretches, pp. 691–694. -/
/- PM-VERBATIM-BEGIN PM3:✱215·01
strʻP=α̂(α⊂CʻP.P̆ʻα∩Pʻα⊂α)
PM-VERBATIM-END PM3:✱215·01 -/
/- PM-VERBATIM-BEGIN PM3:✱215·1
α∈strʻP ≡ α⊂CʻP.P̆ʻα∩Pʻα⊂α
PM-VERBATIM-END PM3:✱215·1 -/
/- PM-VERBATIM-BEGIN PM3:✱215·11
strʻP=strʻP
PM-VERBATIM-END PM3:✱215·11 -/
/- PM-VERBATIM-BEGIN PM3:✱215·13
sectʻP⊂strʻP.sect̆ʻP⊂strʻP
PM-VERBATIM-END PM3:✱215·13 -/
/- PM-VERBATIM-BEGIN PM3:✱215·14
α∈sectʻP.β∈sect̆ʻP ⊃ α∩β∈strʻP
PM-VERBATIM-END PM3:✱215·14 -/
namespace PM.FirstEdition.Volume3.Star215Source
def canonicalSource := "https://archive.org/details/principiamathema03whit/page/691"
def propositionIds := ["215.01","215.1","215.11","215.13","215.14","215.15","215.16",
  "215.161","215.162","215.163","215.164","215.165","215.166","215.17","215.18","215.19",
  "215.2","215.21","215.22","215.23","215.24","215.25","215.3","215.31",
  "215.32","215.33","215.4","215.41","215.42","215.5","215.51",
  "215.52","215.53","215.54","215.541","215.542","215.543"]
def verbatimStatements := ["strʻP=α̂(α⊂CʻP.P̆ʻα∩Pʻα⊂α) Df",
  "⊢:α∈strʻP.≡.α⊂CʻP.P̆ʻα∩Pʻα⊂α","⊢.strʻP=strʻP",
  "⊢.sectʻP⊂strʻP.sect̆ʻP⊂strʻP","⊢:α∈sectʻP.β∈sect̆ʻP.⊃.α∩β∈strʻP",
  "⊢:P∈trans.α∈strʻP.⊃.α∪Pʻα∈sectʻP.α∪P̆ʻα∈sect̆ʻP",
  "⊢:P∈trans.⊃.strʻP=sʻ{sectʻP∩sect̆ʻP}",
  "⊢:P∈connex.α∈sectʻP.β∈sect̆ʻP.E!α∩β.⊃.α=P̆ʻ(α∩β)∪(α∩β).β=Pʻ(α∩β)∪(α∩β)",
  "⊢:P∈trans∩connex...⊃.P̆ʻα=P̆ʻ(α∩β).Pʻβ=Pʻ(α∩β)",
  "⊢:P∈trans∩connex...⊃.Ppŏʻα=Ppŏʻ(α∩β)",
  "⊢:Hp.⊃.minPʻβ=minPʻ(α∩β).maxPʻα=maxPʻ(α∩β)...",
  "⊢:Ppo∈connex...⊃.α=P*̆ʻ(α∩β).β=P*ʻ(α∩β)...",
  "⊢:Ppo∈Ser.α∈sectʻP.β∈sect̆ʻP.α∩β∈1.⊃.α∩β=ιʻmaxPʻα=ιʻminPʻβ",
  "⊢:P∈trans.⊃.P̆ʻα∩Pʻβ∈strʻP","⊢.P(x†y),P(x†−y),P(−x†y),P(−x†−y)∈strʻP",
  "⊢:P²⊂I.x∈CʻP.⊃.ιʻx∈strʻP",
  "⊢:P∈connex.α∈strʻP.x∈α.⊃.P̆ʻα=α−maxPʻα∪P̆ʻx",
  "⊢:P∈connex.α,β∈strʻP.E!α∩β.⊃.α∩β∈strʻP",
  "⊢:α,β∈strʻP.⊃.α∩β∈strʻP","⊢:P∈connex.μ⊂strʻP.E!pʻμ.⊃.sʻμ∈strʻP",
  "⊢:μ⊂strʻP.⊃.CʻP∩pʻμ∈strʻP","⊢:μ⊂strʻP.E!μ.⊃.pʻμ∈strʻP",
  "⊢:P∈connex.α,β∈strʻP−ιʻΛ.α∩β=Λ.⊃.α⊂P̆ʻβ∨β⊂P̆ʻα",
  "⊢:P∈trans∩connex.α∈strʻP.E!minPʻα.E!maxPʻα.⊃.α=P(minPʻα−maxPʻα)",
  "⊢:P∈trans∩connex.α∈strʻP.E!minPʻα.E!seqPʻα.⊃.α=P(minPʻα−seqPʻα)",
  "⊢:P∈trans∩connex.α∈strʻP.E!precPʻα.E!seqPʻα.⊃.α=P(precPʻα−seqPʻα)",
  "⊢:P∈connex.μ∈Cl exclʻ(strʻP−ιʻΛ).⊃.Pcl†μ=Pcl†μ̆",
  "⊢:P∈trans∩connex.μ∈Cl exclʻ(strʻP−ιʻΛ).⊃.Pcl†μ∈Ser",
  "⊢:P∈trans∩connex.μ∈Cl exclʻ(strʻP−ιʻΛ).μ̆∈1.⊃.CʻPcl†μ=P",
  "⊢:P∈trans∩connex.α∈sectʻP.β∈sect̆ʻP.⊃:E!α∩β.limaxPʻα=liminPʻβ.⊃.α∩β∈1",
  "⊢:P∈Ser.α∈sectʻP.β∈sect̆ʻP.α∩β∈1.⊃.limaxPʻα=liminPʻβ=ιʻ(α∩β)",
  "⊢:Hp *215.5.α∩β∈0∪1.E!limaxPʻα.E!liminPʻβ.⊃.liminPʻβ P limaxPʻα",
  "⊢:Hp *215.5.α∩β=Λ.E!limaxPʻα.E!liminPʻβ.⊃.limaxPʻα=liminPʻβ∨limaxPʻα P liminPʻβ",
  "⊢:P∈Ser.α∈sectʻP.β∈sect̆ʻP.α∩β=Λ.α∪β=CʻP.E!limaxPʻα.E!liminPʻβ.⊃.limaxPʻα=liminPʻβ∨limaxPʻα P liminPʻβ",
  "⊢:P∈Ser.α∈sectʻP.β∈sect̆ʻP.α∪β=CʻP.⊃:α∩β∈0∪1.⊃:E!limaxPʻα.≡.E!liminPʻβ",
  "⊢:Hp *215.541.α∩β=Λ.E!limaxPʻα.limaxPʻα∉DʻP1.⊃.limaxPʻα=liminPʻβ",
  "⊢:P∈Ser.α∈sectʻP.β∈sect̆ʻP.α∪β=CʻP.α∩β∈0∪1.E!limaxPʻα.limaxPʻα∉DʻP1.⊃.limaxPʻα=liminPʻβ"]
end PM.FirstEdition.Volume3.Star215Source
