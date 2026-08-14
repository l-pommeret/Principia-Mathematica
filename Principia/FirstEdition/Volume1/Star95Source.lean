/-!
# Principia Mathematica I, ✱95 — equi-factor relation

Canonical witness: Project Gutenberg ebook 78050 and the 1910 Volume I
facsimile, printed pages 627–631 (scan leaves 649–653).
-/

/- PM-VERBATIM-BEGIN PM1:✱95·01
✱95·01. ( P∗Q)=sgʻ{(P∥ Q)_∗} Dft [✱95]
✱95·01. (P∗Q) = sgʻ{(P∥Q)∗} Dft [✱95]
PM-VERBATIM-END PM1:✱95·01 -/
/- PM-VERBATIM-BEGIN PM1:✱95·1
✱95·1. ⊢:: M∈ (P∗Q)ʻR.≡:. R∈ μ:N∈ μ.⊃_N.P| N| Q∈ μ:⊃_μ.M∈ μ
✱95·1. ⊢ :: M∈(P∗Q)ʻR .≡: R∈μ : N∈μ .⊃_N. P|N|Q∈μ :⊃_μ. M∈μ
PM-VERBATIM-END PM1:✱95·1 -/
/- PM-VERBATIM-BEGIN PM1:✱95·11
✱95·11. ⊢:. φ R:φ N.⊃_N.φ(P| N| Q):⊃:M∈ (P∗Q)ʻR.⊃_M.φ M
✱95·11. ⊢ : φR : φN .⊃_N. φ(P|N|Q) :⊃: M∈(P∗Q)ʻR .⊃_M. φM
PM-VERBATIM-END PM1:✱95·11 -/
/- PM-VERBATIM-BEGIN PM1:✱95·12
✱95·12. ⊢:. M∈ (P∗Q)ʻR.⊃_M.φ(P| M| Q):⊃:N∈ (P∗Q)ʻR-ιʻR.⊃_N.φ N
✱95·12. ⊢ : M∈(P∗Q)ʻR .⊃_M. φ(P|M|Q) :⊃: N∈(P∗Q)ʻR−ιʻR .⊃_N. φN
PM-VERBATIM-END PM1:✱95·12 -/
/- PM-VERBATIM-BEGIN PM1:✱95·13
✱95·13. ⊢.R∈ (P∗Q)ʻR [✱95·1]
✱95·13. ⊢ . R∈(P∗Q)ʻR [✱95·1]
PM-VERBATIM-END PM1:✱95·13 -/
/- PM-VERBATIM-BEGIN PM1:✱95·131
✱95·131. ⊢.P| R| Q∈ (P∗Q)ʻR
✱95·131. ⊢ . P|R|Q∈(P∗Q)ʻR
PM-VERBATIM-END PM1:✱95·131 -/
/- PM-VERBATIM-BEGIN PM1:✱95·132
✱95·132. ⊢:M∈ (P ∗ Q)ʻR.⊃.P| M| Q∈ (P ∗ Q)ʻR [✱90·172 P∥ Q/R .✱43·102 ]
✱95·132. ⊢ : M∈(P∗Q)ʻR .⊃. P|M|Q∈(P∗Q)ʻR
PM-VERBATIM-END PM1:✱95·132 -/
/- PM-VERBATIM-BEGIN PM1:✱95·14
✱95·14. ⊢:. φ R:N∈ (P ∗ Q)ʻR.φ N.⊃_N.φ(P| N| Q):⊃:M∈ (P ∗ Q)ʻR.⊃_M.φ M
✱95·14. ⊢ : φR : N∈(P∗Q)ʻR . φN .⊃_N. φ(P|N|Q) :⊃: M∈(P∗Q)ʻR .⊃_M. φM
PM-VERBATIM-END PM1:✱95·14 -/
/- PM-VERBATIM-BEGIN PM1:✱95·21
✱95·21. ⊢:M∈ (P ∗ Q)ʻR.⊃.(∃ S,T).S∈ PotʻP∪ ιʻI.T∈ PotʻQ∪ ιʻI.M=S| R| T
✱95·21. ⊢ : M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotʻP∪ιʻI . T∈PotʻQ∪ιʻI . M=S|R|T
PM-VERBATIM-END PM1:✱95·21 -/
/- PM-VERBATIM-BEGIN PM1:✱95·211
✱95·211. ⊢:ᗡʻR⊂ CʻQ.M ∈ (P ∗ Q)ʻR.⊃. (∃ S,T).S∈ PotʻP∪ ιʻI.T∈ PotidʻQ.M=S| R| T
✱95·211. ⊢ : ᗡʻR⊂CʻQ . M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotʻP∪ιʻI . T∈PotidʻQ . M=S|R|T
PM-VERBATIM-END PM1:✱95·211 -/
/- PM-VERBATIM-BEGIN PM1:✱95·212
✱95·212. ⊢:DʻR ⊂ CʻP.M∈ (P ∗ Q)ʻR.⊃. (∃ S,T).S∈ PotidʻP.T∈ PotʻQ∪ ιʻI.M=S| R| T [Proof as in ✱95·211]
✱95·212. ⊢ : DʻR⊂CʻP . M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotidʻP . T∈PotʻQ∪ιʻI . M=S|R|T [Proof as in ✱95·211]
PM-VERBATIM-END PM1:✱95·212 -/
/- PM-VERBATIM-BEGIN PM1:✱95·22
✱95·22. ⊢:DʻR ⊂ CʻP.ᗡʻR⊂ CʻQ.M∈ (P ∗ Q)ʻR.⊃. (∃ S,T).S∈ PotidʻP.T∈ PotidʻQ.M=S| R| T [Proof as in ✱95·211]
✱95·22. ⊢ : DʻR⊂CʻP . ᗡʻR⊂CʻQ . M∈(P∗Q)ʻR .⊃. (∃S,T) . S∈PotidʻP . T∈PotidʻQ . M=S|R|T [Proof as in ✱95·211]
PM-VERBATIM-END PM1:✱95·22 -/
/- PM-VERBATIM-BEGIN PM1:✱95·221
✱95·221. ⊢:T∈ PotʻQ.⊃.(∃ S).S∈ PotʻP.S| R| T∈ (P ∗ Q)ʻR
✱95·221. ⊢ : T∈PotʻQ .⊃. (∃S) . S∈PotʻP . S|R|T∈(P∗Q)ʻR
PM-VERBATIM-END PM1:✱95·221 -/
/- PM-VERBATIM-BEGIN PM1:✱95·222
✱95·222. ⊢:S∈ PotʻP.⊃.(∃ T).T∈ PotʻQ.S| R| T∈ (P ∗ Q)ʻR [Proof as in ✱95·221]
✱95·222. ⊢ : S∈PotʻP .⊃. (∃T) . T∈PotʻQ . S|R|T∈(P∗Q)ʻR [Proof as in ✱95·221]
PM-VERBATIM-END PM1:✱95·222 -/
/- PM-VERBATIM-BEGIN PM1:✱95·23
✱95·23. ⊢:M∈ (P ∗ Q)ʻR.⊃.M(Pₛₜ| Qₜₛ)R
✱95·23. ⊢ : M∈(P∗Q)ʻR .⊃. M(P_st|Q_ts)R
PM-VERBATIM-END PM1:✱95·23 -/
/- PM-VERBATIM-BEGIN PM1:✱95·24
✱95·24. ⊢:M∈ (P ∗ Q)ʻR.⊃.M(Qₜₛ| Pₛₜ)R [Proof as in ✱95·23]
✱95·24. ⊢ : M∈(P∗Q)ʻR .⊃. M(Q_ts|P_st)R [Proof as in ✱95·23]
PM-VERBATIM-END PM1:✱95·24 -/
/- PM-VERBATIM-BEGIN PM1:✱95·3
✱95·3. ⊢:. ∃̇!R.ᗡʻQ⊂ DʻQ.ᗡʻR⊂ DʻQ.⊃:T∈ PotidʻQ.⊃.∃̇!R| T
✱95·3. ⊢ : ∃̇!R . ᗡʻQ⊂DʻQ . ᗡʻR⊂DʻQ .⊃: T∈PotidʻQ .⊃. ∃̇!(R|T)
PM-VERBATIM-END PM1:✱95·3 -/
/- PM-VERBATIM-BEGIN PM1:✱95·301
✱95·301. ⊢:. ∃̇!R.DʻP⊂ ᗡʻP.DʻR⊂ ᗡʻP.⊃:S∈ PotidʻP.⊃.∃̇!S| R [Proof as in ✱95·3]
✱95·301. ⊢ : ∃̇!R . DʻP⊂ᗡʻP . DʻR⊂ᗡʻP .⊃: S∈PotidʻP .⊃. ∃̇!(S|R) [Proof as in ✱95·3]
PM-VERBATIM-END PM1:✱95·301 -/
/- PM-VERBATIM-BEGIN PM1:✱95·302
✱95·302. ⊢:. ᗡʻQ⊂ DʻQ.ᗡʻR⊂ DʻQ.⊃:T∈ PotidʻQ.⊃.ᗡʻ(R| T)⊂ DʻQ
✱95·302. ⊢ : ᗡʻQ⊂DʻQ . ᗡʻR⊂DʻQ .⊃: T∈PotidʻQ .⊃. ᗡʻ(R|T)⊂DʻQ
PM-VERBATIM-END PM1:✱95·302 -/
/- PM-VERBATIM-BEGIN PM1:✱95·303
✱95·303. ⊢:. DʻR⊂ ᗡʻP.DʻP⊂ ᗡʻP.⊃:S∈ PotidʻP.⊃.Dʻ(S| R)⊂ ᗡʻP [Proof as in ✱95·302]
✱95·303. ⊢ : DʻR⊂ᗡʻP . DʻP⊂ᗡʻP .⊃: S∈PotidʻP .⊃. Dʻ(S|R)⊂ᗡʻP [Proof as in ✱95·302]
PM-VERBATIM-END PM1:✱95·303 -/
/- PM-VERBATIM-BEGIN PM1:✱95·304
✱95·304. ⊢:. ᗡʻQ⊂ DʻQ.ᗡʻR⊂ DʻQ.DʻP⊂ ᗡʻP.DʻR⊂ ᗡʻP.⊃: S∈ PotidʻP.T∈ PotidʻQ.⊃.Dʻ(S| R| T)⊂ ᗡʻP.ᗡʻ(S| R| T)⊂ DʻQ [✱95·302·303.✱34·36]
✱95·304. ⊢ : ᗡʻQ⊂DʻQ . ᗡʻR⊂DʻQ . DʻP⊂ᗡʻP . DʻR⊂ᗡʻP .⊃: S∈PotidʻP . T∈PotidʻQ .⊃. Dʻ(S|R|T)⊂ᗡʻP . ᗡʻ(S|R|T)⊂DʻQ
PM-VERBATIM-END PM1:✱95·304 -/
/- PM-VERBATIM-BEGIN PM1:✱95·305
✱95·305. ⊢:. Hp✱95·304.⊃:M∈ (P ∗ Q)ʻR.⊃.DʻM⊂ ᗡʻP.ᗡʻM⊂ DʻQ [✱95·304·22]
✱95·305. ⊢ : Hp✱95·304 .⊃: M∈(P∗Q)ʻR .⊃. DʻM⊂ᗡʻP . ᗡʻM⊂DʻQ
PM-VERBATIM-END PM1:✱95·305 -/
/- PM-VERBATIM-BEGIN PM1:✱95·32
✱95·32. ⊢:. Hp✱95·31.⊃:M∈ (P ∗ Q)ʻR.⊃.∃̇!M [✱95·31·22]
✱95·32. ⊢ : Hp✱95·31 .⊃: M∈(P∗Q)ʻR .⊃. ∃̇!M
PM-VERBATIM-END PM1:✱95·32 -/
/- PM-VERBATIM-BEGIN PM1:✱95·33
✱95·33. ⊢:ᗡʻR⊂ B⃗ʻQ.⊃.ᗡʻ(S| R| T)⊂ ŤʻʻB⃗ʻQ
✱95·33. ⊢ : ᗡʻR⊂B⃗ʻQ .⊃. ᗡʻ(S|R|T)⊂T̆ʻʻB⃗ʻQ
PM-VERBATIM-END PM1:✱95·33 -/
/- PM-VERBATIM-BEGIN PM1:✱95·34
✱95·34. ⊢:ᗡʻR⊂ B⃗ʻQ.M∈ (P ∗ Q)ʻR.⊃.(∃ T).T∈ PotidʻQ.ᗡʻM⊂ ŤʻʻB⃗ʻQ [✱95·33·211]
✱95·34. ⊢ : ᗡʻR⊂B⃗ʻQ . M∈(P∗Q)ʻR .⊃. (∃T) . T∈PotidʻQ . ᗡʻM⊂T̆ʻʻB⃗ʻQ
PM-VERBATIM-END PM1:✱95·34 -/
/- PM-VERBATIM-BEGIN PM1:✱95·35
✱95·35. ⊢:Q∈ 1→Cls.ᗡʻR⊂ B⃗ʻQ.M∈ (P ∗ Q)ʻR.⊃.(∃ α).α∈ genʻQ.ᗡʻM⊂ α [✱95·34.✱93·32]
✱95·35. ⊢ : Q∈1→Cls . ᗡʻR⊂B⃗ʻQ . M∈(P∗Q)ʻR .⊃. (∃α) . α∈genʻQ . ᗡʻM⊂α
PM-VERBATIM-END PM1:✱95·35 -/
/- PM-VERBATIM-BEGIN PM1:✱95·351
✱95·351. ⊢:. Q∈ 1→Cls.ᗡʻR⊂ B⃗ʻQ.⊃: T, T'∈ PotidʻQ.∃ !ᗡʻ(S| R| T)∩ ᗡʻ(S'| R| T').⊃.T=T'
✱95·351. ⊢ : Q∈1→Cls . ᗡʻR⊂B⃗ʻQ .⊃: T,T'∈PotidʻQ . ∃!ᗡʻ(S|R|T)∩ᗡʻ(S'|R|T') .⊃. T=T'
PM-VERBATIM-END PM1:✱95·351 -/
/- PM-VERBATIM-BEGIN PM1:✱95·352
✱95·352. ⊢:. P∈ Cls→1.DʻR⊂ B⃗ʻP̌.⊃: S, S'∈ PotidʻP.∃ !Dʻ(S| R| T)∩ Dʻ(S'| R| T').⊃.S=S' [Proof as in ✱95·351]
✱95·352. ⊢ : P∈Cls→1 . DʻR⊂B⃗ʻP̆ .⊃: S,S'∈PotidʻP . ∃!Dʻ(S|R|T)∩Dʻ(S'|R|T') .⊃. S=S'
PM-VERBATIM-END PM1:✱95·352 -/
/- PM-VERBATIM-BEGIN PM1:✱95·36
✱95·36. ⊢:. Q∈ 1→Cls.ᗡʻR⊂ B⃗ʻQ.∃̇!R.DʻR⊂ ᗡʻP. DʻP⊂ ᗡʻP.ᗡʻQ⊂ DʻQ.⊃: S, S'∈ PotidʻP.T,T'∈ PotidʻQ.S| R| T=S'| R| T'.⊃.T=T'
✱95·36. ⊢ : Q∈1→Cls . ᗡʻR⊂B⃗ʻQ . ∃̇!R . DʻR⊂ᗡʻP . DʻP⊂ᗡʻP . ᗡʻQ⊂DʻQ .⊃: S,S'∈PotidʻP . T,T'∈PotidʻQ . S|R|T=S'|R|T' .⊃. T=T'
PM-VERBATIM-END PM1:✱95·36 -/
/- PM-VERBATIM-BEGIN PM1:✱95·361
✱95·361. ⊢:. P∈ Cls→1.DʻR ⊂ B⃗ʻP̌.∃̇!R.DʻP⊂ ᗡʻP. ᗡʻR⊂ DʻQ.ᗡʻQ⊂ DʻQ.⊃: S, S'∈ PotidʻP.T, T'∈ PotidʻQ.S| R| T=S'| R| T'.⊃.S=S' [Proof as in ✱95·36]
✱95·361. ⊢ : P∈Cls→1 . DʻR⊂B⃗ʻP̆ . ∃̇!R . DʻP⊂ᗡʻP . ᗡʻR⊂DʻQ . ᗡʻQ⊂DʻQ .⊃: S,S'∈PotidʻP . T,T'∈PotidʻQ . S|R|T=S'|R|T' .⊃. S=S'
PM-VERBATIM-END PM1:✱95·361 -/

namespace PM.FirstEdition.Volume1.Star95Source

abbrev Rel (α : Sort u) := α → α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z

/-- ✱95·01: the least class containing `R` and closed under `M ↦ P|M|Q`. -/
inductive Equi (P Q R : Rel α) : Rel α → Prop
  | base : Equi P Q R R
  | step {M} : Equi P Q R M → Equi P Q R (comp (comp P M) Q)

/-- Editorial name for the exact typed reconstruction of ✱95·01.

`Equi` remains the internal carrier used by later kernels.  Keeping the
numbered declaration as this dedicated transparent alias prevents carrier
occurrences from being misread as historical citations of ✱95·01. -/
abbrev star_95_01 (P Q R : Rel α) : Rel α → Prop := Equi P Q R

end PM.FirstEdition.Volume1.Star95Source

/- PM-VERBATIM-BEGIN PM1:✱95·31
✱95·31. ⊢:. Hp✱95·304.∃̇!R.⊃:S∈ PotidʻP.T∈ PotidʻQ.⊃.∃̇!S| R| T
PM-VERBATIM-END PM1:✱95·31 -/
/- PM-VERBATIM-BEGIN PM1:✱95·37
✱95·37. ⊢:. P∈ Cls→1.Q∈ 1→Cls.DʻR ⊂ B⃗ʻP̌.ᗡʻR⊂ B⃗ʻQ. DʻP⊂ ᗡʻP.ᗡʻQ⊂ DʻQ.⊃: S, S'∈ PotidʻP.T,T'∈ PotidʻQ.S| R| T=S'| R| T'.⊃.S=S'.T=T' [✱95·36·361]
PM-VERBATIM-END PM1:✱95·37 -/
/- PM-VERBATIM-BEGIN PM1:✱95·38
✱95·38. ⊢:. ∃ !B⃗ʻQ∩ ᗡʻR.⊃:T∈ PotʻQ.⊃.R| T ≠ R
PM-VERBATIM-END PM1:✱95·38 -/
/- PM-VERBATIM-BEGIN PM1:✱95·381
✱95·381. ⊢:. ∃ !B⃗ʻP̌∩ DʻR.⊃:S∈ PotʻP.⊃.S| R ≠ R [Proof as in ✱95·38]
PM-VERBATIM-END PM1:✱95·381 -/
/- PM-VERBATIM-BEGIN PM1:✱95·382
✱95·382. ⊢:. ∃ !B⃗ʻP̌ ∩ DʻR.∨.∃ !B⃗ʻQ∩ ᗡʻR:⊃: S∈ PotʻP.T∈ PotʻQ.⊃.S| R| T ≠ R
PM-VERBATIM-END PM1:✱95·382 -/
/- PM-VERBATIM-BEGIN PM1:✱95·383
✱95·383. ⊢:. ∃̇!R:DʻR⊂ B⃗ʻP̌.∨.ᗡʻR⊂ B⃗ʻQ:⊃: S∈ PotʻP.T∈ PotʻQ.⊃.S| R| T ≠ R [✱95·382.✱33·24.✱22·621]
PM-VERBATIM-END PM1:✱95·383 -/
/- PM-VERBATIM-BEGIN PM1:✱95·4
✱95·4. ⊢:M∈ (P ∗ Q)ʻR.S∈ PotʻP.T∈ PotʻQ.S| R| T∈ (P ∗ Q)ʻR.⊃. S| M| T∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·4 -/
/- PM-VERBATIM-BEGIN PM1:✱95·41
✱95·41. ⊢:. P∈ Cls→1.Q∈ 1→Cls.DʻP⊂ ᗡʻP.ᗡʻQ⊂ DʻQ.⊃: S, S'∈ PotidʻP.T, T'∈ PotidʻQ.⊃.Š| S| S'| N| T'| T| Ť = S'| N| T' [✱92·15·151]
PM-VERBATIM-END PM1:✱95·41 -/
/- PM-VERBATIM-BEGIN PM1:✱95·411
✱95·411. ⊢:. Hp✱95·41.⊃: S∈ PotidʻP.T∈ PotidʻQ.M∈ (P ∗ Q)ʻR.⊃.M = Š| S| M| T| Ť [✱95·41·22]
PM-VERBATIM-END PM1:✱95·411 -/
/- PM-VERBATIM-BEGIN PM1:✱95·42
✱95·42. ⊢:. Hp✱95·41.⊃:M∈ (P ∗ Q)ʻR - ιʻR.⊃.P̌| M| Q̌∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·42 -/
/- PM-VERBATIM-BEGIN PM1:✱95·43
✱95·43. ⊢:. Hp✱95·41.Hp✱95·382. ⊃:S∈ PotidʻP.T∈ PotidʻQ. P| S| R| T| Q∈ (P ∗ Q)ʻR.⊃.S| R| T∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·43 -/
/- PM-VERBATIM-BEGIN PM1:✱95·431
✱95·431. ⊢:Hp✱95·43.S∈ PotidʻP.T∈ PotidʻQ.M∈ (P ∗ Q)ʻR. P| S| M| T| Q∈ (P ∗ Q)ʻR.⊃.S| M| T∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·431 -/
/- PM-VERBATIM-BEGIN PM1:✱95·44
✱95·44. ⊢:. Hp✱95·43. S∈ PotidʻP.T∈ PotidʻQ.⊃: M∈ (P ∗ Q)ʻR.S| M| T∈ (P ∗ Q)ʻR.⊃.S| R| T∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·44 -/
/- PM-VERBATIM-BEGIN PM1:✱95·45
✱95·45. ⊢:. Hp✱95·43.S, S'∈ PotidʻP.T, T'∈ PotidʻQ. S| S'| R| T'| T∈ (P ∗ Q)ʻR.⊃:S| R| T∈ (P ∗ Q)ʻR.≡.S'| R| T'∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·45 -/
/- PM-VERBATIM-BEGIN PM1:✱95·46
✱95·46. ⊢:. Hp✱95·41.∃̇!R.DʻR⊂ B⃗ʻP̌.ᗡʻ R⊂ B⃗ʻQ̌.⊃: T∈ PotʻQ.⊃.R| T∼∈ (P ∗ Q)ʻR
PM-VERBATIM-END PM1:✱95·46 -/
/- PM-VERBATIM-BEGIN PM1:✱95·47
✱95·47. ⊢:Hp✱95·46.S∈ PotidʻP.T, T'∈ PotidʻQ. S| R| T,S| R| T'∈ (P ∗ Q)ʻR.⊃.T=T'
PM-VERBATIM-END PM1:✱95·47 -/
/- PM-VERBATIM-BEGIN PM1:✱95·471
✱95·471. ⊢:Hp✱95·46.S, S'∈ PotidʻP.T∈ PotidʻQ. S| R| T,S'| R| T∈ (P ∗ Q)ʻR.⊃.S=S' [Proof as in ✱95·47]
PM-VERBATIM-END PM1:✱95·471 -/
/- PM-VERBATIM-BEGIN PM1:✱95·51
✱95·51. ⊢:Hp✱95·46.M, M'∈ (P ∗ Q)ʻR.∃ !ᗡʻM∩ ᗡʻM'.⊃.M=M'
PM-VERBATIM-END PM1:✱95·51 -/
/- PM-VERBATIM-BEGIN PM1:✱95·511
✱95·511. ⊢:Hp✱95·46.M, M'∈ (P ∗ Q)ʻR.∃ !DʻM∩ DʻM'.⊃.M=M' [Proof as in ✱95·51]
PM-VERBATIM-END PM1:✱95·511 -/
/- PM-VERBATIM-BEGIN PM1:✱95·52
✱95·52. ⊢:P, Q, R∈ 1→1.DʻP⊂ ᗡʻP.ᗡʻQ ⊂ DʻQ.DʻR⊂ B⃗ʻP̌.ᗡʻR⊂ B⃗ʻQ.⊃. ṡʻ(P ∗ Q)ʻR∈ 1→1
PM-VERBATIM-END PM1:✱95·52 -/
/- PM-VERBATIM-BEGIN PM1:✱95·6
✱95·6. ⊢:DʻR⊂ ᗡʻP.DʻP⊂ ᗡʻP.ᗡʻR= B⃗ʻQ.Q∈ 1→Cls.⊃. ᗡʻʻ(P ∗ Q)ʻR=genʻQ
PM-VERBATIM-END PM1:✱95·6 -/
/- PM-VERBATIM-BEGIN PM1:✱95·601
✱95·601. ⊢:ᗡʻR⊂ DʻQ.ᗡʻQ⊂ DʻQ.DʻR=B⃗ʻP̌.P∈ Cls→1.⊃. Dʻʻ(P ∗ Q)ʻR=genʻP̌ [Proof as in ✱95·6]
PM-VERBATIM-END PM1:✱95·601 -/
/- PM-VERBATIM-BEGIN PM1:✱95·61
✱95·61. ⊢:P,Q,R∈ 1→1.DʻP⊂ ᗡʻP.ᗡʻQ⊂ DʻQ.DʻR=B⃗ʻP̌.ᗡʻR=B⃗ʻQ.⊃. ṡʻ(P ∗ Q)ʻR∈ 1→1.Dʻṡʻ(P ∗ Q)ʻR=sʻgenʻP̌.ᗡʻṡʻ(P ∗ Q)ʻR=sʻgenʻQ [✱95·52·6·601.✱41·43·44]
PM-VERBATIM-END PM1:✱95·61 -/
/- PM-VERBATIM-BEGIN PM1:✱95·62
✱95·62. ⊢:Hp✱95·61.⊃.sʻgenʻP sm sʻgenʻQ [✱95·61.✱73·2]
PM-VERBATIM-END PM1:✱95·62 -/
/- PM-VERBATIM-BEGIN PM1:✱95·63
✱95·63. ⊢:P, Q∈ 1→1.ᗡʻP⊂ DʻP.ᗡʻQ⊂ DʻQ. B⃗ʻP sm B⃗ʻQ.⊃. sʻgenʻP sm sʻgenʻQ
PM-VERBATIM-END PM1:✱95·63 -/
/- PM-VERBATIM-BEGIN PM1:✱95·64
✱95·64. ⊢:P, Q∈ 1→1.ᗡʻP⊂ DʻP.ᗡʻQ⊂ DʻQ.B⃗ʻP sm B⃗ʻQ. pʻᗡʻʻPotʻP=Λ.pʻᗡʻʻPotʻQ=Λ.⊃.DʻP sm DʻQ [✱95·63.✱93·274.✱33·181]
PM-VERBATIM-END PM1:✱95·64 -/
/- PM-VERBATIM-BEGIN PM1:✱95·65
✱95·65. ⊢: P,Q∈ 1→1.ᗡʻP⊂ DʻP.ᗡʻQ⊂ DʻQ.B⃗ʻP sm B⃗ʻQ. CʻP=P̌_∗ʻʻB⃗ʻP.CʻQ=Q̌_∗ʻʻB⃗ʻQ.⊃.CʻP sm CʻQ [✱95·63.✱93·36]
PM-VERBATIM-END PM1:✱95·65 -/
/- PM-VERBATIM-BEGIN PM1:✱95·7
✱95·7. ⊢:R, S∈ 1→1.ᗡʻR⊂ DʻS.ᗡʻS⊂ DʻR.⊃.B⃗ʻ(R| S) sm B⃗ʻ(S| R)
PM-VERBATIM-END PM1:✱95·7 -/
/- PM-VERBATIM-BEGIN PM1:✱95·71
✱95·71. ⊢:R, S∈ 1→1.ᗡʻR⊂ DʻS.ᗡʻS⊂ DʻR.⊃.sʻgenʻ(R| S) sm sʻgenʻ(S| R)
PM-VERBATIM-END PM1:✱95·71 -/
