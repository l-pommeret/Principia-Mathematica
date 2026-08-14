/-! PM II ✱111, first macro-lot, pp. 88–92. -/
namespace PM.FirstEdition.Volume2.Star111Source
/- PM-VERBATIM-BEGIN PM2:✱111·01
✱111·01. κ sm sm λ=(1→1)∩α̂Ŝα∩T̂(κ=T̆ʻλ) Df
PM-VERBATIM-END PM2:✱111·01 -/
/- PM-VERBATIM-BEGIN PM2:✱111·02
✱111·02. Crp(S)ʻβ=(Sʻβ) sm β Df
PM-VERBATIM-END PM2:✱111·02 -/
/- PM-VERBATIM-BEGIN PM2:✱111·1
✱111·1. ⊢:T∈κ sm sm λ.≡.T∈1→1.Sʻλ⊂αʻT.κ=T̆ʻλ
PM-VERBATIM-END PM2:✱111·1 -/
/- PM-VERBATIM-BEGIN PM2:✱111·11
✱111·11. ⊢:T∈κ sm sm λ.⊃.T∈1→1
PM-VERBATIM-END PM2:✱111·11 -/
/- PM-VERBATIM-BEGIN PM2:✱111·112
✱111·112. ⊢:T∈κ sm sm λ.⊃.T∈κ sm λ∩Rlʻsm
PM-VERBATIM-END PM2:✱111·112 -/
/- PM-VERBATIM-BEGIN PM2:✱111·12
✱111·12. ⊢:sʻλ⊂α.⊃.(T↾α)̆ʻλ=T̆ʻλ
PM-VERBATIM-END PM2:✱111·12 -/
/- PM-VERBATIM-BEGIN PM2:✱111·121
✱111·121. ⊢.(T↾sʻλ)̆ʻλ=T̆ʻλ
PM-VERBATIM-END PM2:✱111·121 -/
/- PM-VERBATIM-BEGIN PM2:✱111·13
✱111·13. ⊢:T∈κ sm sm λ.≡.T̆∈λ sm sm κ
PM-VERBATIM-END PM2:✱111·13 -/
/- PM-VERBATIM-BEGIN PM2:✱111·131
✱111·131. ⊢:T∈κ sm sm λ.≡.T̆∈λ sm sm κ
PM-VERBATIM-END PM2:✱111·131 -/
/- PM-VERBATIM-BEGIN PM2:✱111·14
✱111·14. ⊢:T↾sʻλ∈κ sm sm λ.≡.T↾sʻλ∈1→1.sʻλ⊂αʻT.κ=T̆ʻλ
PM-VERBATIM-END PM2:✱111·14 -/
/- PM-VERBATIM-BEGIN PM2:✱111·21
✱111·21. ⊢:E!Crp(S)ʻβ.≡.Sʻβ sm β
PM-VERBATIM-END PM2:✱111·21 -/
/- PM-VERBATIM-BEGIN PM2:✱111·221
✱111·221. ⊢:S∈1→Cls.S⊂sm.⊃:E!Crp(S)ʻβ.≡.β∈α†S
PM-VERBATIM-END PM2:✱111·221 -/
/- PM-VERBATIM-BEGIN PM2:✱111·23
✱111·23. ⊢:S∈1→1.β∈αʻS.⊃.Crp(S)ʻβ=ConvʻCrp(S)ʻSʻβ
PM-VERBATIM-END PM2:✱111·23 -/
/- PM-VERBATIM-BEGIN PM2:✱111·451
✱111·451. ⊢:κ sm sm λ.≡.λ sm sm κ
PM-VERBATIM-END PM2:✱111·451 -/
/- PM-VERBATIM-BEGIN PM2:✱111·452
✱111·452. ⊢:κ sm sm λ.λ sm sm μ.⊃.κ sm sm μ
PM-VERBATIM-END PM2:✱111·452 -/
def canonicalSource := "https://archive.org/details/PrincipiaMathematicaVol2/page/n111"
def propositionIds := ["111.01","111.02","111.1","111.11","111.112","111.12",
  "111.121","111.13","111.131","111.14","111.15","111.16","111.18","111.201","111.21",
  "111.211","111.221","111.23","111.25","111.31","111.32","111.321",
  "111.33","111.34","111.4","111.401","111.402","111.43","111.44","111.45",
  "111.451","111.452","111.46","111.47","111.5","111.51","111.52","111.53"]
def verbatimStatements := ["κ sm sm λ=(1→1)∩α̂Ŝα∩T̂(κ=T̆ʻλ) Df",
  "Crp(S)ʻβ=(Sʻβ) sm β Df","⊢:T∈κ sm sm λ.≡.T∈1→1.Sʻλ⊂αʻT.κ=T̆ʻλ",
  "⊢:T∈κ sm sm λ.⊃.T∈1→1","⊢:T∈κ sm sm λ.⊃.T∈κ sm λ∩Rlʻsm",
  "⊢:sʻλ⊂α.⊃.(T↾α)̆ʻλ=T̆ʻλ","⊢.(T↾sʻλ)̆ʻλ=T̆ʻλ",
  "⊢:T∈κ sm sm λ.≡.T̆∈λ sm sm κ","⊢:T∈κ sm sm λ.≡.T̆∈λ sm sm κ",
  "⊢:T↾sʻλ∈κ sm sm λ.≡.T↾sʻλ∈1→1.sʻλ⊂αʻT.κ=T̆ʻλ",
  "⊢:T↾sʻλ∈κ sm sm λ.≡.T↾sʻλ∈(sʻκ)α sm(sʻλ).T∈κ sm λ",
  "⊢:α sm β.γ sm δ.⊃.α=γ.β=δ","⊢.α sm β⊂(α†β)₄ʻβ",
  "⊢:E!Crp(S)ʻβ.≡.E!((Sʻβ)smβ)","⊢:E!Crp(S)ʻβ.≡.Sʻβ sm β",
  "⊢:E!Crp(S)ʻβ.⊃.E!Sʻβ.β∈αʻS","⊢:S∈1→Cls.S⊂sm.⊃:E!Crp(S)ʻβ.≡.β∈α†S",
  "⊢:S∈1→1.β∈αʻS.⊃.Crp(S)ʻβ=ConvʻCrp(S)ʻSʻβ",
  "⊢:S∈1→Cls.S⊂sm.λ⊂αʻS.⊃.Crp(S)ʻʻλ∈Cls ex² excl",
  "⊢:λ,Sʻκ∈Cls² excl.S∈1→1.R∈∈ΔʻCrp(S)ʻκ.⊃.DʻR sm sʻκ",
  "⊢:κ,Sʻλ∈Cls² excl.S∈1→1.R∈∈ΔʻCrp(S)ʻλ.M=sʻDʻR.⊃.M sm sʻλ",
  "⊢:κ,Sʻλ∈Cls² excl.S∈1→1.E!∈ΔʻCrp(S)ʻλ.⊃.E!κ sm sm λ",
  "⊢:Mult ax.⊃:S∈1→1.S⊂sm.κ,λ∈Cls² excl.κ=Sʻλ.λ⊂αʻS.⊃.κ sm sm λ",
  "⊢:Mult ax.⊃:κ sm sm λ.≡.λ sm sm κ",
  "⊢:κ sm sm λ.≡.(∃T).T∈1→1.Sʻλ⊂αʻT.κ=T̆ʻλ.≡.E!κ sm sm λ",
  "⊢:κ sm sm λ.≡.(αT).T∈1→1.Sʻλ⊂αʻT.κ=T̆ʻλ",
  "⊢:κ sm sm λ.≡.(αT).T↾sʻλ∈1→1.Sʻλ⊂αʻT.κ=T̆ʻλ",
  "⊢:κ sm sm λ.⊃.(∃S).S∈1→1.S⊂sm.DʻS=κ.GʻS=λ",
  "⊢:κ sm sm λ.⊃.κ sm λ.sʻκ sm Sʻλ","⊢.λ sm sm λ",
  "⊢:κ sm sm λ.≡.λ sm sm κ","⊢:κ sm sm λ.λ sm sm μ.⊃.κ sm sm μ",
  "⊢:λ,Sʻκ∈Cls² excl.S∈1→1.E!∈ΔʻCrp(S)ʻκ.⊃.Sʻκ sm sm κ",
  "⊢:κ sm sm λ.⊃:κ∈Cls² excl.≡.λ∈Cls² excl",
  "⊢:Mult ax.⊃:κ,λ∈Cls² excl.⊃.E!κ sm λ∩Rlʻsm",
  "⊢:Mult ax.κ,λ∈Cls² excl.E!κ sm λ∩Rlʻsm.⊃.sʻκ sm Sʻλ",
  "⊢:μ,ν∈NC.κ,λ∈μ∩Clʻν.⊃.E!κ sm λ∩Rlʻsm",
  "⊢:Mult ax.μ,ν∈NC.κ,λ∈μ∩Cl exclʻν.⊃.κ sm sm λ"]
end PM.FirstEdition.Volume2.Star111Source
