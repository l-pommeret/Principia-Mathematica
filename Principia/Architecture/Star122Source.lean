/-!
# PM II ✱122 — progressions, opening macro-lot

Canonical Gutenberg 78255, volume II pp. 256–259. Inventory: ✱122·01, ·1,
·11, ·12, ·14, ·141, ·142, ·143, ·15, ·151, ·152, ·16, ·17, ·2,
·21, ·22, ·23, ·231.
-/
/- PM-VERBATIM-BEGIN PM2:✱122·01
✱122·01. Prog = (1→1)∩R̂(DʻR = R̅_*ʻBʻR) Df
PM-VERBATIM-END PM2:✱122·01 -/
/- PM-VERBATIM-BEGIN PM2:✱122·1
✱122·1. ⊢ : R∈Prog .≡. R∈1→1 . DʻR=R̅_*ʻBʻR
PM-VERBATIM-END PM2:✱122·1 -/
/- PM-VERBATIM-BEGIN PM2:✱122·11
✱122·11. ⊢ : R∈Prog .≡: R∈1→1 . E!BʻR : x∈DʻR .≡_x. x∈R̅_*ʻBʻR
PM-VERBATIM-END PM2:✱122·11 -/
/- PM-VERBATIM-BEGIN PM2:✱122·12
✱122·12. ⊢ :: R∈Prog .≡: R∈1→1 . E!BʻR : x∈DʻR .≡_x: BʻR∈α . R̆ʻʻα⊂α .⊃_α. x∈α
PM-VERBATIM-END PM2:✱122·12 -/
/- PM-VERBATIM-BEGIN PM2:✱122·14
✱122·14. ⊢ : R∈Prog .⊃. R̅_poʻBʻR=ᗡʻR
PM-VERBATIM-END PM2:✱122·14 -/
/- PM-VERBATIM-BEGIN PM2:✱122·141
✱122·141. ⊢ : R∈Prog .⊃. ᗡʻR⊂DʻR . CʻR=DʻR
PM-VERBATIM-END PM2:✱122·141 -/
/- PM-VERBATIM-BEGIN PM2:✱122·142
✱122·142. ⊢ : R∈Prog . P∈PotʻR .⊃. DʻP=DʻR
PM-VERBATIM-END PM2:✱122·142 -/
/- PM-VERBATIM-BEGIN PM2:✱122·143
✱122·143. ⊢ : R∈Prog . P∈PotʻR .⊃. ᗡʻP⊂DʻP
PM-VERBATIM-END PM2:✱122·143 -/
/- PM-VERBATIM-BEGIN PM2:✱122·15
✱122·15. ⊢ : R∈Prog .⊃. R=(R⃖∗ʻBʻR)↿R=R↾(R⃖poʻBʻR)=R↾(R⃖∗ʻBʻR)
PM-VERBATIM-END PM2:✱122·15 -/
/- PM-VERBATIM-BEGIN PM2:✱122·151
✱122·151. ⊢ : R∈Prog .⊃. R∗=(R⃖∗ʻBʻR)↿R∗=R∗↾(R⃖∗ʻBʻR)
PM-VERBATIM-END PM2:✱122·151 -/
namespace PM.Architecture.Star122Source
def canonicalSource : String :=
 "https://www.gutenberg.org/files/78255/78255-h/78255-h.htm#Page_256"
def propositionIds : List String :=
 ["122.01","122.1","122.11","122.12","122.14","122.141","122.142",
  "122.143","122.15","122.151","122.152","122.16","122.17","122.2",
  "122.21","122.22","122.23","122.231"]
end PM.Architecture.Star122Source
