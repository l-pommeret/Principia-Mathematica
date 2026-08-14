/-! # PM I ✱91 — powers of a relation (PG78050, opening) -/
/- PM-VERBATIM-BEGIN PM1:✱91·01
✱91·01. Rₛₜ=(R|)_∗ Df
✱91·01. R_st = (R|)_* Df
PM-VERBATIM-END PM1:✱91·01 -/
/- PM-VERBATIM-BEGIN PM1:✱91·02
✱91·02. Rₜₛ=(| R)_∗ Df
✱91·02. R_ts = (|R)_* Df
PM-VERBATIM-END PM1:✱91·02 -/
/- PM-VERBATIM-BEGIN PM1:✱91·03
✱91·03. PotʻR=R⃗ₜₛʻR Df
✱91·03. PotʻR = →R_tsʻR Df
PM-VERBATIM-END PM1:✱91·03 -/
/- PM-VERBATIM-BEGIN PM1:✱91·04
✱91·04. PotidʻR=R⃗ₜₛʻ(I↾ CʻR) Df
✱91·04. PotidʻR = →R_tsʻ(I↾CʻR) Df
PM-VERBATIM-END PM1:✱91·04 -/
/- PM-VERBATIM-BEGIN PM1:✱91·05
✱91·05. Rₚₒ=ṡʻPotʻR Df
✱91·05. R_po = ṡʻPotʻR Df
PM-VERBATIM-END PM1:✱91·05 -/
/- PM-VERBATIM-BEGIN PM1:✱91·1
✱91·1. ⊢:: PRₛₜQ.≡:. S∈ μ.⊃_S.R| S∈ μ:Q∈ μ:⊃_μ.P∈ μ
Dem.
⊢.*4·2.(*91·01).⊃
⊢:: PRₛₜQ. ≡:. P(R| )_∗Q:.
[*90·11] ≡:. P∈ Cʻ(R| ):(R| )ʻʻμ⊂ μ.Q∈ μ.⊃_μ.P∈ μ:.
[*43·3.*33·161] ≡:. (R| )ʻʻμ⊂ μ.Q∈ μ.⊃_μ.P∈ μ:.
[*37·61] ≡:. S∈ μ.⊃_S.R| ʻS∈ μ:Q∈ μ:⊃_μ.P∈ μ:.
[*43·11] ≡:. S∈ μ.⊃_S.R| S∈ μ:Q∈ μ:⊃_μ.P∈ μ:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·1 -/
/- PM-VERBATIM-BEGIN PM1:✱91·11
✱91·11. ⊢:: PRₜₛQ.≡:. S∈ μ.⊃_S.S| R∈ μ:Q∈ μ:⊃_μ.P∈ μ
✱91·11. ⊢ :: P R_ts Q .≡:. S∈μ .⊃ₛ. S|R∈μ : Q∈μ :⊃μ. P∈μ
PM-VERBATIM-END PM1:✱91·11 -/
/- PM-VERBATIM-BEGIN PM1:✱91·12
✱91·12. ⊢:P∈ PotʻR.≡.PRₜₛR [✱32·18.(✱91·03)]
✱91·12. ⊢ : P∈PotʻR .≡. P R_ts R
PM-VERBATIM-END PM1:✱91·12 -/
/- PM-VERBATIM-BEGIN PM1:✱91·13
✱91·13. ⊢:: P∈ PotʻR.≡:. S∈ μ.⊃_S.S| R∈ μ:R∈ μ:⊃_μ.P∈ μ [✱91·11·12]
✱91·13. ⊢ :: P∈PotʻR .≡:. S∈μ .⊃ₛ. S|R∈μ : R∈μ :⊃μ. P∈μ
PM-VERBATIM-END PM1:✱91·13 -/
/- PM-VERBATIM-BEGIN PM1:✱91·14
✱91·14. ⊢:P∈ PotidʻR.≡.PRₜₛ(I↾ CʻR) [✱32·18.(✱91·04)]
✱91·14. ⊢ : P∈PotidʻR .≡. P R_ts (I↾CʻR)
PM-VERBATIM-END PM1:✱91·14 -/
/- PM-VERBATIM-BEGIN PM1:✱91·15
✱91·15. ⊢:: P∈ PotidʻR.≡:. S∈ μ.⊃_S.S| R∈ μ:I↾ CʻR∈ μ:⊃_μ.P∈ μ [✱91·11·14]
✱91·15. ⊢ :: P∈PotidʻR .≡:. S∈μ .⊃ₛ. S|R∈μ : I↾CʻR∈μ :⊃μ. P∈μ
PM-VERBATIM-END PM1:✱91·15 -/
/- PM-VERBATIM-BEGIN PM1:✱91·16
✱91·16. ⊢:: xRₚₒy.≡:. (∃ P):. S∈ μ.⊃_S.S| R∈ μ:R∈ μ:⊃_μ.P∈ μ:. xPy [✱41·11.(✱91·05).✱91·13]
✱91·16. ⊢ :: x R_po y .≡:. (∃P): P∈PotʻR . xPy
PM-VERBATIM-END PM1:✱91·16 -/
/- PM-VERBATIM-BEGIN PM1:✱91·17
✱91·17. ⊢:. P∈ PotidʻR:φ S.⊃_S.φ(S| R):φ(I↾ CʻR):⊃.φ P
✱91·17. ⊢ :. P∈PotidʻR : φS .⊃ₛ. φ(S|R) : φ(I↾CʻR) :⊃. φP
PM-VERBATIM-END PM1:✱91·17 -/
/- PM-VERBATIM-BEGIN PM1:✱91·171
✱91·171. ⊢:. P∈ PotʻR:φ S.⊃_S.φ(S| R):φ R:⊃.φ P
✱91·171. ⊢ :. P∈PotʻR : φS .⊃ₛ. φ(S|R) : φR :⊃. φP
PM-VERBATIM-END PM1:✱91·171 -/
/- PM-VERBATIM-BEGIN PM1:✱91·2
✱91·2. ⊢:QRₜₛP.⊃.(Q| R)RₜₛP
Dem.
⊢.*43·101.(*91·02).⊃⊢:Hp. ⊃.(Q| R)(| R)Q.Q(| R)_∗P.
[*90·172] ⊃.(Q| R)(| R)_∗P.
[Id.(*91·02)] ⊃.(Q| R)RₜₛP:⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·2 -/
/- PM-VERBATIM-BEGIN PM1:✱91·201
✱91·201. ⊢:QRₛₜP.⊃.(R| Q)RₛₜP [Proof as in ✱91·2]
✱91·201. ⊢ : Q R_st P .⊃. (R|Q) R_st P
PM-VERBATIM-END PM1:✱91·201 -/
/- PM-VERBATIM-BEGIN PM1:✱91·204
✱91·204. ⊢:P{Rₜₛ| (| R)}Q.≡.PRₜₛ(Q| R)
Dem.
⊢.*34·1.⊃⊢:P{Rₜₛ| (| R)}Q. ≡.(∃ T).PRₜₛT.T(| R)Q.
[*43·101] ≡.(∃ T).PRₜₛT.T=Q| R.
[*13·195] ≡.PRₜₛ(Q| R):⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·204 -/
/- PM-VERBATIM-BEGIN PM1:✱91·205
✱91·205. ⊢:P{Rₛₜ| (R| )}Q.≡.PRₛₜ(R| Q)
✱91·205. ⊢ : P{R_st|(R|)}Q .≡. P R_st (R|Q)
PM-VERBATIM-END PM1:✱91·205 -/
/- PM-VERBATIM-BEGIN PM1:✱91·21
✱91·21. ⊢.Rₜₛ=I⊍Rₜₛ| (| R)
Dem.
⊢.*90·31.(*91·02).⊃⊢.Rₜₛ =I↾ Cʻ(| R)⊍Rₜₛ| (| R)
[*43·311] =I⊍Rₜₛ| (| R).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·21 -/
/- PM-VERBATIM-BEGIN PM1:✱91·211
✱91·211 ⊢ . Rₛₜ=I⊍ Rₛₜ| (R|)
✱91·211. ⊢ . R_st = I ⊍ R_st | (R|)
PM-VERBATIM-END PM1:✱91·211 -/
/- PM-VERBATIM-BEGIN PM1:✱91·212
✱91·212 ⊢ :. PRₜₛQ. ≡ :P=Q. ∨ . PRₜₛ(Q| R)
Dem.
⊢.*91·21.*50·1. ⊃ ⊢ :. PRₜₛQ. ≡ :P=Q. ∨ . P{Rₜₛ| (| R)}Q:
[*91·204] ≡ :P=Q. ∨ . PRₜₛ(Q| R):. ⊃ ⊢.Prop
PM-VERBATIM-END PM1:✱91·212 -/
/- PM-VERBATIM-BEGIN PM1:✱91·213
✱91·213 ⊢ :. PRₛₜQ. ≡ :P=Q. ∨ . PRₛₜ(R| Q)
✱91·213. ⊢ : P R_st Q .≡: P=Q .∨. P R_st (R|Q)
PM-VERBATIM-END PM1:✱91·213 -/
/- PM-VERBATIM-BEGIN PM1:✱91·22
✱91·22 ⊢ . R⃗ₜₛʻQ=ι ʻQ∪ R⃗ₜₛʻ(Q| R) [✱91·212.✱32·18.✱51·15]
✱91·22. ⊢ . →R_tsʻQ = ιʻQ ∪ →R_tsʻ(Q|R)
PM-VERBATIM-END PM1:✱91·22 -/
/- PM-VERBATIM-BEGIN PM1:✱91·221
✱91·221 ⊢ . R⃗ₛₜʻQ=ι ʻQ∪ R⃗ₛₜʻ(R| Q)
✱91·221. ⊢ . →R_stʻQ = ιʻQ ∪ →R_stʻ(R|Q)
PM-VERBATIM-END PM1:✱91·221 -/
/- PM-VERBATIM-BEGIN PM1:✱91·23
✱91·23. ⊢.PotidʻR=ιʻ(I↾ CʻR)∪ PotʻR
Dem.
⊢. *91·2.(*91·04). ⊃ ⊢ . PotidʻR =ι ʻ(I↾ CʻR)∪ R⃗ₜₛʻ{(I↾ CʻR)| R}
[*50·65.(*91·03)] =ι ʻ(I↾ CʻR)∪ PotʻR. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱91·23 -/
/- PM-VERBATIM-BEGIN PM1:✱91·231
✱91·231 ⊢ . R⃗ₜₛʻI=ι ʻI∪ PotʻR [✱91·22.(✱91·03).✱50·4]
✱91·231. ⊢ . →R_tsʻI = ιʻI ∪ PotʻR
PM-VERBATIM-END PM1:✱91·231 -/
/- PM-VERBATIM-BEGIN PM1:✱91·24
✱91·24. ⊢.PotʻR=| RʻʻPotidʻR
Dem.
⊢.*91·12. ⊃ ⊢ :P∈ PotʻR. ≡ . PRₜₛR.
[*50·65] ≡ . PRₜₛ(I↾ CʻR| R).
[*91·204] ≡ . P{Rₜₛ| (| R)}(I↾ CʻR).
[*90·32.(*91·02)] ≡ . P{(| R)| Rₜₛ}(I↾ CʻR).
[*37·3] ≡ . P∈ | RʻʻR⃗ₜₛʻ(I↾ CʻR).
[*4·2.(*91·04)] ≡ . P∈ | RʻʻPotidʻR:⊃ ⊢ .Prop
PM-VERBATIM-END PM1:✱91·24 -/
/- PM-VERBATIM-BEGIN PM1:✱91·241
✱91·241 ⊢ :TRₜₛP. ⊃ . (Q| T)Rₜₛ(Q| P)
Dem.
⊢.*91·212. ⊃ ⊢ . (Q| P)Rₜₛ(Q| P) (1)
⊢.*91·2. ⊃ ⊢ :(Q| S)Rₜₛ(Q| P). ⊃ . (Q| S| R)Rₜₛ(Q| P) (2)
⊢.(1).(2).*91·11 Ŝ{(Q| S)Rₜₛ(Q| P)}/μ . ⊃ ⊢.Prop
PM-VERBATIM-END PM1:✱91·241 -/
/- PM-VERBATIM-BEGIN PM1:✱91·242
✱91·242. ⊢:SRₜₛ(Q| P).⊃.S∈ Q| ʻʻR⃗ₜₛʻP
Dem.
⊢.*91·22.*43·11. ⊃⊢.Q| P∈ Q| ʻʻR⃗ₜₛʻP (1)
⊢.*37·1.*43·1.⊃
⊢:S∈ Q| ʻʻRₜₛʻP. ≡.(∃ T).T∈ R⃗ₜₛʻP.S=Q| T.
[*91·2] ⊃.(∃ T).T| R∈ R⃗ₜₛʻP.S| R=Q| T| R.
[*37·1.*43·1] ⊃.S| R∈ Q| ʻʻR⃗ₜₛʻP (2)
⊢.(1).(2).*91·11 Q| ʻʻR⃗ₜₛʻP/μ .⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·242 -/
/- PM-VERBATIM-BEGIN PM1:✱91·25
✱91·25. ⊢.R⃗ₜₛʻ(Q| P)=Q| ʻʻR⃗ₜₛʻP
Dem.
⊢.*91·242. ⊃⊢.R⃗ₜₛʻ(Q| P)⊂ Q| ʻʻR⃗ₜₛʻP (1)
⊢.*91·241. ⊃⊢:T∈ R⃗ₜₛʻP.S=Q| T.⊃.S∈ R⃗ₜₛʻ(Q| P):
[*10·11·23] ⊃⊢:(∃ T).T∈ R⃗ₜₛʻP.S=Q| T.⊃.S∈ R⃗ₜₛʻ(Q| P):
[*37·1.*43·1] ⊃⊢:S∈ Q| ʻʻR⃗ₜₛʻP.⊃.S∈ R⃗ₜₛʻ(Q| P) (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·25 -/
/- PM-VERBATIM-BEGIN PM1:✱91·251
✱91·251. ⊢.R⃗ₛₜʻ(Q| P)=| PʻʻR⃗ₛₜʻQ [Proof as in ✱91·25]
✱91·251. ⊢ . →R_stʻ(Q|P) = |Pʻʻ→R_stʻQ
PM-VERBATIM-END PM1:✱91·251 -/
/- PM-VERBATIM-BEGIN PM1:✱91·26
✱91·26. ⊢.R⃗ₜₛʻQ=Q| ʻʻR⃗ₜₛʻI [✱91·25 I/P ]
✱91·26. ⊢ . →R_tsʻQ = Q|ʻʻ→R_tsʻI
PM-VERBATIM-END PM1:✱91·26 -/
/- PM-VERBATIM-BEGIN PM1:✱91·261
✱91·261. ⊢.R⃗ₛₜʻQ=| QʻʻR⃗ₛₜʻI [✱91·251 I, Q/Q, P ]
✱91·261. ⊢ . →R_stʻQ = |Qʻʻ→R_stʻI
PM-VERBATIM-END PM1:✱91·261 -/
/- PM-VERBATIM-BEGIN PM1:✱91·262
✱91·262. ⊢:ᗡʻQ⊂ CʻR.⊃.R⃗ₜₛʻQ=Q| ʻʻPotidʻR [✱91·25 I↾ CʻR/P .✱50·62.(✱91·04) ]
✱91·262. ⊢ : ᗡʻQ⊂CʻR .⊃. →R_tsʻQ = Q|ʻʻPotidʻR
PM-VERBATIM-END PM1:✱91·262 -/
/- PM-VERBATIM-BEGIN PM1:✱91·263
✱91·263. ⊢.R⃗ₜₛʻ(Q| R)=Q| ʻʻPotʻR [✱91·25 R/P. (✱91·03) ]
✱91·263. ⊢ . →R_tsʻ(Q|R) = Q|ʻʻPotʻR
PM-VERBATIM-END PM1:✱91·263 -/
/- PM-VERBATIM-BEGIN PM1:✱91·264
✱91·264. ⊢.PotʻR=ιʻR∪ R| ʻʻPotʻR [✱91·22·263 R/Q ]
✱91·264. ⊢ . PotʻR = ιʻR ∪ R|ʻʻPotʻR
PM-VERBATIM-END PM1:✱91·264 -/
/- PM-VERBATIM-BEGIN PM1:✱91·27
✱91·27. ⊢:P∈ PotidʻR.⊃.CʻP⊂ CʻR
Dem.
⊢.*50·5·52. ⊃⊢.Cʻ(I↾ CʻR)=CʻR.
[*22·42] ⊃⊢.Cʻ(I↾ CʻR)⊂ CʻR (1)
⊢.*34·38. ⊃⊢:CʻS⊂ CʻR.⊃.Cʻ(S| R)⊂ CʻR (2)
⊢.(1).(2).*91·17 CʻS⊂ CʻR/φ S .⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·27 -/
/- PM-VERBATIM-BEGIN PM1:✱91·271
✱91·271. ⊢:P∈ PotʻR.⊃.DʻP⊂ DʻR.ᗡʻP⊂ ᗡʻR
Dem.
⊢.*22·42.⊃⊢.DʻR⊂ DʻR.ᗡʻR⊂ ᗡʻR (1)
⊢.*34·36.⊃⊢:DʻS⊂ DʻR.⊃.Dʻ(S| R)⊂ DʻR.ᗡʻ(S| R)⊂ ᗡʻR (2)
⊢.(1).(2).*91·17 DʻS⊂ DʻR.ᗡʻS⊂ ᗡʻR/φ S .⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·271 -/
/- PM-VERBATIM-BEGIN PM1:✱91·28
✱91·28. ⊢:P∈ PotidʻR.⊃.P| R∈ PotʻR [✱91·24]
✱91·28. ⊢ : P∈PotidʻR .⊃. P|R∈PotʻR
PM-VERBATIM-END PM1:✱91·28 -/
/- PM-VERBATIM-BEGIN PM1:✱91·281
✱91·281. ⊢:PotʻR⊂ PotidʻR.| RʻʻPotidʻR⊂ PotidʻR [✱91·23·24]
✱91·281. ⊢ : PotʻR⊂PotidʻR . |RʻʻPotidʻR⊂PotidʻR
PM-VERBATIM-END PM1:✱91·281 -/
/- PM-VERBATIM-BEGIN PM1:✱91·282
✱91·282. ⊢:P∈ PotʻR.⊃.P| R∈ PotʻR
✱91·282. ⊢ : P∈PotʻR .⊃. P|R∈PotʻR
PM-VERBATIM-END PM1:✱91·282 -/
/- PM-VERBATIM-BEGIN PM1:✱91·283
✱91·283. ⊢:| RʻʻPotʻR⊂ PotʻR [✱91·282]
✱91·283. ⊢ : |RʻʻPotʻR⊂PotʻR
PM-VERBATIM-END PM1:✱91·283 -/
/- PM-VERBATIM-BEGIN PM1:✱91·3
✱91·3. ⊢:P∈ PotidʻR.⊃.R| P=P| R
Dem.
⊢.*50·64·65.⊃⊢.R| I↾ CʻR=I↾ CʻR| R (1)
⊢.*34·21. ⊃⊢.R| (S| R)=(R| S)| R (2)
⊢.*34·27. ⊃⊢:R| S=S| R.⊃.(R| S)| R=(S| R)| R.
[(2)] ⊃.R| (S| R)=(S| R)| R (3)
⊢.*91·17 R| S=S| R/φ S .⊃
⊢:. P∈ PotidʻR:R| S=S| R.⊃_S.R| (S| R)=(S| R)| R:R| I↾ CʻR=I↾ CʻR| R:
⊃.R| P=P| R (4)
⊢.(1).(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·3 -/
/- PM-VERBATIM-BEGIN PM1:✱91·301
✱91·301. ⊢:P∈ R⃗ₛₜʻ(I↾ CʻR).⊃.R| P=P| R [Proof as in ✱91·3]
✱91·301. ⊢ : P∈→R_stʻ(I↾CʻR) .⊃. R|P=P|R
PM-VERBATIM-END PM1:✱91·301 -/
/- PM-VERBATIM-BEGIN PM1:✱91·302
✱91·302. ⊢.| RʻʻPotidʻR=R| ʻʻPotidʻR
Dem.
⊢.*91·3.*13·182.⊃⊢:. P∈ PotidʻR. ⊃:S=R| P.≡.S=P| R:
[*43·1·101] ⊃:S(R| )P.≡.S(| R)P (1)
⊢.(1).*5·32. ⊃⊢:P∈ PotidʻR.S(R| )P.≡.P∈ PotidʻR.S(| R)P:
[*10·11·281]⊃⊢: (∃ P).P∈ PotidʻR.S(R| )P.≡.
(∃ P).P∈ PotidʻR.S(| R)P:
[*37·1] ⊃⊢:S∈ R| ʻʻPotidʻR.≡.S∈ | RʻʻPotidʻR:⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·302 -/
/- PM-VERBATIM-BEGIN PM1:✱91·303
✱91·303. ⊢.| RʻʻR⃗ₛₜʻ(I↾ CʻR)=R| ʻʻR⃗ₛₜʻ(I↾ CʻR) [Proof as in ✱91·302]
✱91·303. ⊢ . |Rʻʻ→R_stʻ(I↾CʻR)=R|ʻʻ→R_stʻ(I↾CʻR)
PM-VERBATIM-END PM1:✱91·303 -/
/- PM-VERBATIM-BEGIN PM1:✱91·304
✱91·304. ⊢.| RʻʻPotʻR=R| ʻʻPotʻR [Proof as in ✱91·302]
✱91·304. ⊢ . |RʻʻPotʻR=R|ʻʻPotʻR
PM-VERBATIM-END PM1:✱91·304 -/
/- PM-VERBATIM-BEGIN PM1:✱91·31
✱91·31. ⊢.PotʻR=R| ʻʻPotidʻR [✱91·24·301]
✱91·31. ⊢ . PotʻR=R|ʻʻPotidʻR
PM-VERBATIM-END PM1:✱91·31 -/
/- PM-VERBATIM-BEGIN PM1:✱91·33
✱91·33. ⊢.PotidʻR=R⃗ₛₜʻ(I↾ CʻR)
Dem.
⊢.*91·23. ⊃⊢.I↾ CʻR∈ PotidʻR (1)
⊢.*91·3. ⊃⊢:P∈ PotidʻR. ⊃.R| P=P| R.
[*91·281] ⊃.R| P∈ PotidʻR (2)
⊢.(1).(2).*91·1 PotidʻR/μ . ⊃⊢:PRₛₜ(I↾ CʻR).⊃.P∈ PotidʻR (3)
⊢.*91·301.⊃⊢:PRₛₜ(I↾ CʻR). ⊃.P| R=R| P.
[*91·201] ⊃.(P| R)Rₛₜ(I↾ CʻR) (4)
⊢.*91·213. ⊃⊢.(I↾ CʻR)Rₛₜ(I↾ CʻR) (5)
⊢.(4).(5).*91·17. ⊃⊢:P∈ PotidʻR.⊃.PRₛₜ(I↾ CʻR) (6)
⊢.(3).(6). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·33 -/
/- PM-VERBATIM-BEGIN PM1:✱91·331
✱91·331. ⊢.PotʻR=R⃗ₛₜʻR
Dem.
⊢.*91·24·33.⊃⊢.PotʻR =| RʻʻR⃗ₛₜʻ(I↾ CʻR)
[*91·251.*50·65] =R⃗ₛₜʻR.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·331 -/
/- PM-VERBATIM-BEGIN PM1:✱91·34
✱91·34. ⊢:P, Q∈ PotidʻR.⊃.P| Q=Q| P
Dem.
*50·62.*91·27. ⊃⊢:P∈ PotidʻR.⊃.P| (I↾ CʻR)=P
[*50·63.*91·27] =(I↾ CʻR)| P (1)
⊢.*34·27. ⊃⊢:P∈ PotidʻR.P| S=S| P.⊃.P| S| R=S| P| R
[*91·3] =S| R| P (2)
⊢.(1).(2).*91·17 P| S=S| P/φ S .⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·34 -/
/- PM-VERBATIM-BEGIN PM1:✱91·341
✱91·341. ⊢:P, Q∈ PotidʻR.⊃.P| Q∈ PotidʻR
Dem.
⊢.*50·62.*91·27. ⊃⊢:P∈ PotidʻR.⊃.P| (I↾ CʻR)=P.
[*13·12] ⊃.P| (I↾ CʻR)∈ PotidʻR (1)
⊢.*91·281. ⊃⊢:P| S∈ PotidʻR.⊃.P| S| R∈ PotidʻR (2)
⊢.(1).(2).*91·17 P| S∈ PotidʻR/φ S .⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·341 -/
/- PM-VERBATIM-BEGIN PM1:✱91·342
✱91·342. ⊢:P∈ PotidʻR.Q∈ PotʻR.⊃.P| Q∈ PotʻR
Dem.
⊢.*91·28. ⊃⊢:P∈ PotidʻR.⊃.P| R∈ PotʻR (1)
⊢.*91·282. ⊃⊢:P| Q∈ PotʻR.⊃.P| Q| R∈ PotʻR (2)
⊢.(1).(2).*91·171.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·342 -/
/- PM-VERBATIM-BEGIN PM1:✱91·343
✱91·343. ⊢:P, Q∈ PotʻR.⊃.P| Q∈ PotʻR [✱91·342·23]
✱91·343. ⊢ : P,Q∈PotʻR .⊃. P|Q∈PotʻR
PM-VERBATIM-END PM1:✱91·343 -/
/- PM-VERBATIM-BEGIN PM1:✱91·35
✱91·35. ⊢.I↾ CʻR∈ PotidʻR [✱91·23]
✱91·35. ⊢ . I↾CʻR∈PotidʻR
PM-VERBATIM-END PM1:✱91·35 -/
/- PM-VERBATIM-BEGIN PM1:✱91·351
✱91·351. ⊢.R∈ PotʻR [✱91·264]
✱91·351. ⊢ . R∈PotʻR
PM-VERBATIM-END PM1:✱91·351 -/
/- PM-VERBATIM-BEGIN PM1:✱91·352
✱91·352. ⊢.R²∈ PotʻR [✱91·282·351]
✱91·352. ⊢ . R²∈PotʻR
PM-VERBATIM-END PM1:✱91·352 -/
/- PM-VERBATIM-BEGIN PM1:✱91·36
✱91·36. ⊢:P∈ PotʻR.⊃.P| R,R| P∈ PotʻR [✱91·343·351]
✱91·36. ⊢ : P∈PotʻR .⊃. P|R,R|P∈PotʻR
PM-VERBATIM-END PM1:✱91·36 -/
/- PM-VERBATIM-BEGIN PM1:✱91·37
✱91·37. ⊢:. PotidʻR⊂ μ.≡:I↾ CʻR∈ μ:S∈ PotidʻR.S∈ μ.⊃_S.S| R∈ μ
Dem.
⊢.*91·281·35.⊃
⊢:. I↾ CʻR∈ μ:S∈ PotidʻR.S∈ μ.⊃_S.S| R∈ μ:≡:
I↾ CʻR∈ PotidʻR.I↾ CʻR∈ μ:S∈ PotidʻR.S∈ μ.⊃_S.S| R∈ PotidʻR.S| R∈ μ:
[*91·17]⊃:P∈ PotidʻR.⊃.P∈ μ (1)
⊢.*91·35. ⊃⊢:PotidʻR⊂ μ.⊃.I↾ CʻR∈ μ (2)
⊢.*91·281.⊃⊢:. PotidʻR⊂ μ.⊃:S∈ PotidʻR.⊃_S.S| R∈ μ:
[*3·41] ⊃:S∈ PotidʻR.S∈ μ.⊃_S.S| R∈ μ (3)
⊢.(1).(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·37 -/
/- PM-VERBATIM-BEGIN PM1:✱91·371
✱91·371. ⊢:. P∈ Potidʻ R.⊃_P.φ P:≡: φ(I↾ CʻR):S∈ PotidʻR.φ S.⊃_S.φ(S| R) [✱91·37]
✱91·371. ⊢ : P∈PotidʻR .⊃ₚ. φP :≡: φ(I↾CʻR) : S∈PotidʻR.φS .⊃ₛ. φ(S|R)
PM-VERBATIM-END PM1:✱91·371 -/
/- PM-VERBATIM-BEGIN PM1:✱91·372
✱91·372. ⊢:. PotʻR⊂ μ.≡:R∈ μ:S∈ PotʻR.S∈ μ.⊃_S.S| R∈ μ [Proof as in ✱91·37]
✱91·372. ⊢ : PotʻR⊂μ .≡: R∈μ : S∈PotʻR.S∈μ .⊃ₛ. S|R∈μ
PM-VERBATIM-END PM1:✱91·372 -/
/- PM-VERBATIM-BEGIN PM1:✱91·373
✱91·373. ⊢:. P∈ PotʻR.⊃_P.φ P:≡:φ R:S∈ PotʻR.φ S.⊃_S.φ(S| R)
✱91·373. ⊢ : P∈PotʻR .⊃ₚ. φP :≡: φR : S∈PotʻR.φS .⊃ₛ. φ(S|R)
PM-VERBATIM-END PM1:✱91·373 -/
/- PM-VERBATIM-BEGIN PM1:✱91·41
✱91·41. ⊢.R⃗ₜₛʻ(P| R)=P| ʻʻPotʻR [✱91·25 P, R/Q, P.(✱91·03) ]
✱91·41. ⊢ . →R_tsʻ(P|R)=P|ʻʻPotʻR
PM-VERBATIM-END PM1:✱91·41 -/
/- PM-VERBATIM-BEGIN PM1:✱91·411
✱91·411. ⊢.R⃗ₛₜʻ(R| P)=| PʻʻPotʻR [✱91·251 R/Q.✱91·331 ]
✱91·411. ⊢ . →R_stʻ(R|P)=|PʻʻPotʻR
PM-VERBATIM-END PM1:✱91·411 -/
/- PM-VERBATIM-BEGIN PM1:✱91·42
✱91·42. ⊢.R⃗ₜₛʻP=ιʻP∪ P| ʻʻPotʻR [✱91·22·41]
✱91·42. ⊢ . →R_tsʻP=ιʻP∪P|ʻʻPotʻR
PM-VERBATIM-END PM1:✱91·42 -/
/- PM-VERBATIM-BEGIN PM1:✱91·421
✱91·421. ⊢.R⃗ₛₜʻP=ιʻP∪ | PʻʻPotʻR [✱91·221·411]
✱91·421. ⊢ . →R_stʻP=ιʻP∪|PʻʻPotʻR
PM-VERBATIM-END PM1:✱91·421 -/
/- PM-VERBATIM-BEGIN PM1:✱91·43
✱91·43. ⊢:P∈ PotʻR.QRₜₛP.⊃.Q∈ PotʻR
Dem.
⊢.*91·42. ⊃⊢:. Hp.⊃:Q=P.∨.Q∈ P| ʻʻPotʻR:
[*37·1.*43·101] ⊃:Q=P.∨.(∃ T).T∈ PotʻR.Q=P| T:
[*13·12.*91·343] ⊃:Q∈ PotʻR:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·43 -/
/- PM-VERBATIM-BEGIN PM1:✱91·431
✱91·431. ⊢:P∈ PotidʻR.QRₜₛP.⊃.Q∈ PotidʻR [Proof as in ✱91·43]
✱91·431. ⊢ : P∈PotidʻR . Q R_ts P .⊃. Q∈PotidʻR
PM-VERBATIM-END PM1:✱91·431 -/
/- PM-VERBATIM-BEGIN PM1:✱91·44
✱91·44. ⊢:. P, Q∈ PotidʻR.⊃:QRₜₛP.∨ .PRₜₛQ
Dem.
⊢.*91·14. ⊃⊢:P∈ PotidʻR.⊃.PRₜₛ(I↾ CʻR) (1)
⊢.*91·2. ⊃⊢:QRₜₛP.⊃.(Q| R)RₜₛP (2)
⊢.*91·212. ⊃⊢:. PRₜₛQ.⊃:P=Q.∨ .PRₜₛ(Q| R) (3)
⊢.*91·212. ⊃⊢:P=Q.⊃.QRₜₛP.
[*91·2] ⊃.(Q| R)RₜₛP (4)
⊢.(3).(4). ⊃⊢:. PRₜₛQ.⊃:(Q| R)RₜₛP.∨ .PRₜₛ(Q| R) (5)
⊢.(2).(5). ⊃⊢:. QRₜₛP.∨ .PRₜₛQ:⊃:(Q| R)RₜₛP.∨ .PRₜₛ(Q| R) (6)
⊢.(1).(6).*91·17.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·44 -/
/- PM-VERBATIM-BEGIN PM1:✱91·45
✱91·45. ⊢:. P, Q∈ PotidʻR.⊃:(∃ T):T∈ PotidʻR:Q=P| T.∨ .P=Q| T
Dem.
⊢.*91·262·27.⊃⊢:. Hp. ⊃:R⃗ₜₛʻP=P| ʻʻPotidʻR.R⃗ₜₛʻQ=Q| ʻʻPotidʻR:
[*37·1.*43·1] ⊃:QRₜₛP.≡.(∃ T).T∈ PotidʻR.Q=P| T:
PRₜₛQ.≡.(∃ T).T∈ PotidʻR.P=Q| T (1)
⊢.(1).*91·44.*10·42.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·45 -/
/- PM-VERBATIM-BEGIN PM1:✱91·46
✱91·46. ⊢:. P, Q∈ PotidʻR.⊃:(∃ T):T∈ PotidʻR:Q=T| P.∨ .P=T| Q [✱91·45·34]
✱91·46. ⊢ : P,Q∈PotidʻR .⊃: (∃T): T∈PotidʻR : Q=T|P .∨. P=T|Q
PM-VERBATIM-END PM1:✱91·46 -/
/- PM-VERBATIM-BEGIN PM1:✱91·502
✱91·502. ⊢.R⪽Rₚₒ
✱91·502. ⊢ . R ⊂ R_po
PM-VERBATIM-END PM1:✱91·502 -/
/- PM-VERBATIM-BEGIN PM1:✱91·503
✱91·503. ⊢.R²⪽Rₚₒ [✱91·352.(✱91·05).✱41·13]
✱91·503. ⊢ . R² ⊂ R_po
PM-VERBATIM-END PM1:✱91·503 -/
/- PM-VERBATIM-BEGIN PM1:✱91·504
✱91·504. ⊢.DʻRₚₒ=DʻR.ᗡʻRₚₒ=ᗡʻR.CʻRₚₒ=CʻR
Dem.
⊢.*91·502. ⊃⊢.DʻR⊂ DʻRₚₒ (1)
⊢.*91·271.*40·43. ⊃⊢.sʻDʻʻPotʻR⊂ DʻR.
[*41·43] ⊃⊢.DʻRₚₒ⊂ DʻR (2)
⊢.(1).(2). ⊃⊢.DʻR=DʻRₚₒ (3)
Similarly ⊢.ᗡʻR=ᗡʻRₚₒ.CʻR=CʻRₚₒ (4)
⊢.(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·504 -/
/- PM-VERBATIM-BEGIN PM1:✱91·51
✱91·51. ⊢.Rₚₒ| R=R| Rₚₒ
Dem.
⊢.*43·421.(*91·05).⊃⊢.Rₚₒ| R =ṡʻ| RʻʻPotʻR
[*91·304] =ṡʻR| ʻʻPotʻR
[*43·42.(*91·05)] =R| Rₚₒ.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·51 -/
/- PM-VERBATIM-BEGIN PM1:✱91·511
✱91·511. ⊢.Rₚₒ| R⪽Rₚₒ
✱91·511. ⊢ . R_po|R⊂R_po
PM-VERBATIM-END PM1:✱91·511 -/
/- PM-VERBATIM-BEGIN PM1:✱91·512
✱91·512. ⊢.Rₚₒ⪽R_∗| R
Dem.
⊢.*90·32. ⊃⊢.R⪽R_∗| R (1)
⊢.*90·16. ⊃⊢:S⪽R_∗| R.⊃.S⪽R_∗.
[*34·34] ⊃.S| R⪽R_∗| R (2)
⊢.(1).(2).*91·171 S⪽R_∗| R/φ S. ⊃⊢:P∈ PotʻR.⊃.P⪽R_∗| R:
[*41·151.(*91·05)] ⊃⊢.Rₚₒ⪽R_∗| R.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·512 -/
/- PM-VERBATIM-BEGIN PM1:✱91·513
✱91·513. ⊢.R_∗⪽ṡʻPotidʻR
Dem.
⊢.*90·112 x(ṡʻPotidʻR)z/φ z .⊃
⊢:. xR_∗y:x(ṡʻPotidʻR)z.zRw.⊃z,w.x(ṡʻPotidʻR)w:
x(ṡʻPotidʻR)x:⊃.x(ṡʻPotidʻR)y (1)
⊢.*43·421. ⊃⊢.(ṡʻPotidʻR)| R=ṡʻ| RʻʻPotidʻR
[*91·281.*41·161] ⪽ṡʻPotidʻR.
[*34·1.*10·23]⊃⊢:x(ṡʻPotidʻR)z.zRw. ⊃z,w.x(ṡʻPotidʻR)w (2)
⊢.*90·13. ⊃⊢:xR_∗y.⊃.x∈ CʻR.
[*50·3.*35·101] ⊃.x(I↾ CʻR)x.
[*91·35.*41·13] ⊃.x(ṡʻPotidʻR)x (3)
⊢.(2).(3).*4·71·73. ⊃⊢:Hp(1).≡.xR_∗y (4)
⊢.(1).(4). ⊃⊢:xR_∗y.⊃.x(ṡʻPotidʻR)y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·513 -/
/- PM-VERBATIM-BEGIN PM1:✱91·514
✱91·514. ⊢.R_∗| R⪽Rₚₒ
Dem.
⊢.*91·513.⊃⊢.R_∗| R ⪽(ṡʻPotidʻR)| R
[*43·421] ⪽(ṡʻ| RʻʻPotidʻR
[*91·24] ⪽ṡʻPotʻR
[(*91·05] ⪽Rₚₒ.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·514 -/
/- PM-VERBATIM-BEGIN PM1:✱91·52
✱91·52. ⊢.Rₚₒ=R_∗| R=R| R_∗
✱91·52. ⊢ . R_po=R_*|R=R|R_*
PM-VERBATIM-END PM1:✱91·52 -/
/- PM-VERBATIM-BEGIN PM1:✱91·521
✱91·521. ⊢ : P ∈ PotidʻR. ≡ . P̌ ∈ PotidʻŘ
Dem.
⊢ . *91·15 Cnvʻʻμ/μ . ⊃⊢ :: P̌ ∈ PotidʻŘ . ⊃ :.
I↾ CʻR ∈ Cnvʻʻμ:S∈ Cnvʻʻμ.⊃_S.S| Ř∈ Cnvʻʻμ:⊃.P̌∈ Cnvʻʻμ (1)
⊢ . *72·513.11. ⊃⊢ : P̌∈ Cnvʻʻμ . ≡ . P∈ μ (2)
⊢ . (2). *50·5·51. ⊃⊢ : I↾ CʻR ∈ Cnvʻʻμ . ≡ . I↾ CʻR ∈ μ (3)
⊢ . *31·51. ⊃⊢ :. S ∈ Cnvʻʻμ . ⊃_S. S| Ř ∈ Cnvʻʻμ :≡:
Š∈ Cnvʻʻμ. ⊃_S. Š| Ř ∈ Cnvʻʻμ :
[(2).*34·2] ≡ : S ∈ μ. ⊃_S . R | S ∈ μ (4)
⊢ . (1) . (2). (3). (4). ⊃
⊢ :: P̌ ∈ PotidʻŘ . ⊃:. I↾ CʻR∈ μ: S∈ μ .⊃_S . S| R∈ μ:⊃.P∈ μ (5)
⊢ . (5). *10·11·21 .*91·15. ⊃
⊢ : P̌ ∈ PotidʻŘ. ⊃ . P ∈ PotidʻR (6)
⊢ .(6) P̌,Ř/P, R.*31·33. ⊃⊢:P∈ PotidʻR.⊃.P̌∈ PotidʻŘ (7)
⊢ . (6) . (7). ⊃⊢ . Prop
PM-VERBATIM-END PM1:✱91·521 -/
/- PM-VERBATIM-BEGIN PM1:✱91·522
✱91·522. ⊢: P ∈ PotʻR .≡. P̌ ∈ PotʻŘ [Proof as in ✱91·521]
✱91·522. ⊢ : P∈PotʻR .≡. P̌∈PotʻŘ
PM-VERBATIM-END PM1:✱91·522 -/
/- PM-VERBATIM-BEGIN PM1:✱91·53
✱91·53. ⊢. Řₚₒ = (Ř)ₚₒ
Dem.
⊢. *91·52. ⊃⊢. Řₚₒ = Ř| Ř_∗
[*90·132] = Ř| (Ř)_∗
[*91·52] = (Ř)ₚₒ. ⊃⊢ . Prop
PM-VERBATIM-END PM1:✱91·53 -/
/- PM-VERBATIM-BEGIN PM1:✱91·54
✱91·54. ⊢.R_∗=I↾ CʻR⊍Rₚₒ
✱91·54. ⊢ . R_*=I↾CʻR⊍R_po
PM-VERBATIM-END PM1:✱91·54 -/
/- PM-VERBATIM-BEGIN PM1:✱91·541
✱91·541. ⊢ . R_∗∩̇J=Rₚₒ∩̇J [✱25·401.(✱50·02).✱35·441. ✱91·54]
✱91·541. ⊢ . R_*∩̇J=R_po∩̇J
PM-VERBATIM-END PM1:✱91·541 -/
/- PM-VERBATIM-BEGIN PM1:✱91·542
✱91·542. ⊢:xR_∗y.x ≠ y.≡.xRₚₒy.x ≠ y
✱91·542. ⊢ : xR_*y.x≠y .≡. xR_po y.x≠y
PM-VERBATIM-END PM1:✱91·542 -/
/- PM-VERBATIM-BEGIN PM1:✱91·543
✱91·543. ⊢ . R_∗ʻʻβ = (β ∩ CʻR) ∪ Rₚₒʻʻβ
Dem.
⊢ . *91·54.*37·221.⊃⊢.R_∗ʻʻβ = (I↾ CʻR)ʻʻβ ∪ Rₚₒʻʻβ
[*50·59] = (β ∩ CʻR) ∪ Rₚₒʻʻβ.⊃⊢. Prop
PM-VERBATIM-END PM1:✱91·543 -/
/- PM-VERBATIM-BEGIN PM1:✱91·544
✱91·544. ⊢ . Ř_∗ʻʻβ = (β ∩ CʻR) ∪ Řₚₒʻʻβ
✱91·544. ⊢ . Ř_*ʻʻβ=(β∩CʻR)∪Ř_poʻʻβ
PM-VERBATIM-END PM1:✱91·544 -/
/- PM-VERBATIM-BEGIN PM1:✱91·545
✱91·545. ⊢ : β ⊂ CʻR.⊃. R_∗ʻʻβ = β ∪ Rₚₒʻʻβ [✱91·543.✱22·621]
✱91·545. ⊢ : β⊂CʻR .⊃. R_*ʻʻβ=β∪R_poʻʻβ
PM-VERBATIM-END PM1:✱91·545 -/
/- PM-VERBATIM-BEGIN PM1:✱91·546
✱91·546. ⊢ : β ⊂ CʻR. ⊃ . Ř_∗ʻʻβ = β ∪ Řₚₒʻʻβ
✱91·546. ⊢ : β⊂CʻR .⊃. Ř_*ʻʻβ=β∪Ř_poʻʻβ
PM-VERBATIM-END PM1:✱91·546 -/
/- PM-VERBATIM-BEGIN PM1:✱91·55
✱91·55. ⊢.R_∗=ṡʻPotidʻR
Dem.
⊢.*91·23.⊃⊢.ṡʻPotidʻR =ṡʻ{ιʻ(I↾ CʻR)∪ PotʻR}
[*53·17.(*91·05)] =I↾ CʻR⊍Rₚₒ
[*91·54] =R_∗.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·55 -/
/- PM-VERBATIM-BEGIN PM1:✱91·56
✱91·56. ⊢.Rₚₒ²⪽Rₚₒ
Dem.
⊢.*91·52.⊃⊢.Rₚₒ² =R_∗| R| R_∗| R
[*90·16] ⪽R_∗| R_∗| R
[*90·17] ⪽R_∗| R
[*91·52] ⪽Rₚₒ.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·56 -/
/- PM-VERBATIM-BEGIN PM1:✱91·561
✱91·561. ⊢:. S⪽Rₚₒ.T⪽Rₚₒ.⊃.S| T⪽Rₚₒ [✱34·34.✱91·56]
✱91·561. ⊢ : S⊂R_po.T⊂R_po .⊃. S|T⊂R_po
PM-VERBATIM-END PM1:✱91·561 -/
/- PM-VERBATIM-BEGIN PM1:✱91·562
✱91·562. ⊢:S⪽Rₚₒ.⊃.S| R⪽Rₚₒ.R| S⪽Rₚₒ [✱91·561·502]
✱91·562. ⊢ : S⊂R_po .⊃. S|R⊂R_po . R|S⊂R_po
PM-VERBATIM-END PM1:✱91·562 -/
/- PM-VERBATIM-BEGIN PM1:✱91·57
✱91·57. ⊢.Rₚₒ=R⊍Rₚₒ| R=R⊍R| Rₚₒ [✱90·32.✱91·52]
✱91·57. ⊢ . R_po=R⊍R_po|R=R⊍R|R_po
PM-VERBATIM-END PM1:✱91·57 -/
/- PM-VERBATIM-BEGIN PM1:✱91·571
✱91·571. ⊢.Rₚₒ| R=R| Rₚₒ [✱91·52]
✱91·571. ⊢ . R_po|R=R|R_po
PM-VERBATIM-END PM1:✱91·571 -/
/- PM-VERBATIM-BEGIN PM1:✱91·572
✱91·572. ⊢.Rₚₒ-̇(Rₚₒ| R)⪽R [✱91·57.✱22·9·43]
✱91·572. ⊢ . R_po−̇(R_po|R)⊂R
PM-VERBATIM-END PM1:✱91·572 -/
/- PM-VERBATIM-BEGIN PM1:✱91·573
✱91·573. ⊢.Rₚₒ-̇(R| Rₚₒ)⪽R [✱91·571·572]
✱91·573. ⊢ . R_po−̇(R|R_po)⊂R
PM-VERBATIM-END PM1:✱91·573 -/
/- PM-VERBATIM-BEGIN PM1:✱91·574
✱91·574. ⊢.R_∗| Rₚₒ=Rₚₒ| R_∗=Rₚₒ=R| R_∗=R_∗| R
Dem.
⊢.*91·52.⊃⊢.R_∗| Rₚₒ =R_∗| R_∗| R
[*90·17] =R_∗| R (1)
⊢.*91·52.⊃⊢.Rₚₒ| R_∗ =R| R_∗| R_∗
[*90·17] =R| R_∗ (2)
⊢.(1).(2).*91·52.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·574 -/
/- PM-VERBATIM-BEGIN PM1:✱91·58
✱91·58. ⊢:P∈ PotidʻR.⊃.P⪽R_∗ [✱91·55.✱41·13]
✱91·58. ⊢ : P∈PotidʻR .⊃. P⊂R_*
PM-VERBATIM-END PM1:✱91·58 -/
/- PM-VERBATIM-BEGIN PM1:✱91·581
✱91·581. ⊢:P∈ PotʻR.⊃.P⪽Rₚₒ [✱41·13.(✱91·05)]
✱91·581. ⊢ : P∈PotʻR .⊃. P⊂R_po
PM-VERBATIM-END PM1:✱91·581 -/
/- PM-VERBATIM-BEGIN PM1:✱91·59
✱91·59. ⊢:R⪽S.⊃.Rₚₒ⪽Sₚₒ
Dem.
⊢.*90·18.⊃⊢:Hp. ⊃.R_∗⪽S_∗.
[*34·34] ⊃.R_∗| R⪽S_∗| S.
[*91·52] ⊃.Rₚₒ⪽Sₚₒ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·59 -/
/- PM-VERBATIM-BEGIN PM1:✱91·6
✱91·6. ⊢:Q∈ PotʻR.⊃.PotʻQ⊂ PotʻR.Qₚₒ⪽Rₚₒ
Dem.
⊢.*91·171 Q, S∈ PotʻR/R, φ S .⊃
⊢:. P∈ PotʻQ:S∈ PotʻR. ⊃_S.S| Q∈ PotʻR:Q∈ PotʻR:⊃.P∈ PotʻR (1)
⊢.*91·343. ⊃⊢:. Q∈ PotʻR.⊃:S∈ PotʻR.⊃_S| Q∈ PotʻR (2)
⊢.(1).(2). ⊃⊢:P∈ PotʻQ.Q∈ PotʻR.⊃.P∈ PotʻR:
[Exp.*10·11·21] ⊃⊢:Q∈ PotʻR.⊃.PotʻQ⊂ PotʻR. (3)
[*41·161] ⊃.Qₚₒ⪽Rₚₒ (4)
⊢.(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·6 -/
/- PM-VERBATIM-BEGIN PM1:✱91·601
✱91·601. ⊢.(Rₚₒ)ₚₒ=Rₚₒ
Dem.
⊢.*91·502. ⊃⊢.Rₚₒ⪽(Rₚₒ)ₚₒ (1)
⊢.*91·171 Rₚₒ, S⪽Rₚₒ/R, φ S .⊃
⊢:. P∈ PotʻRₚₒ:S⪽Rₚₒ. ⊃_S.S| Rₚₒ⪽Rₚₒ:Rₚₒ⪽Rₚₒ:⊃.P⪽Rₚₒ (2)
⊢.*34·34.*91·56. ⊃⊢:S⪽Rₚₒ.⊃_S.S| Rₚₒ⪽Rₚₒ (3)
⊢.(2).(3).*23·42. ⊃⊢:P∈ PotʻRₚₒ.⊃.P⪽Rₚₒ:
[*41·151] ⊃⊢.(Rₚₒ)ₚₒ⪽Rₚₒ (4)
⊢.(1).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·601 -/
/- PM-VERBATIM-BEGIN PM1:✱91·602
✱91·602. ⊢.(Rₚₒ)_∗=R_∗
Dem.
⊢.*91·54.⊃⊢.(Rₚₒ)_∗ =I↾ CʻRₚₒ⊍(Rₚₒ)ₚₒ
[*91·504·601] =I↾ CʻR⊍Rₚₒ
[*91·54] =R_∗.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·602 -/
/- PM-VERBATIM-BEGIN PM1:✱91·603
✱91·603. ⊢.(R_∗)ₚₒ=R_∗
Dem.
⊢.*91·52.⊃⊢.(R_∗)ₚₒ =(R_∗)_∗| R_∗
[*90·4] =R_∗| R_∗
[*90·17] =R_∗.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·603 -/
/- PM-VERBATIM-BEGIN PM1:✱91·62
✱91·62. ⊢:. xRₚₒy.≡:Řʻʻμ⊂ μ.R⃖ʻx⊂ μ.⊃_μ.y∈ μ [✱91·52.✱90·36]
✱91·62. ⊢ : xR_po y .≡: Řʻʻμ⊂μ . ←Rʻx⊂μ .⊃μ. y∈μ
PM-VERBATIM-END PM1:✱91·62 -/
/- PM-VERBATIM-BEGIN PM1:✱91·7
✱91·7. ⊢.RₚₒʻʻᗡʻR=DʻR.ŘₚₒʻʻDʻR=ᗡʻR [✱91·504.✱37·25]
✱91·7. ⊢ . R_poʻʻᗡʻR=DʻR . Ř_poʻʻDʻR=ᗡʻR
PM-VERBATIM-END PM1:✱91·7 -/
/- PM-VERBATIM-BEGIN PM1:✱91·71
✱91·71. ⊢:Rʻʻμ⊂ μ.≡.Rₚₒʻʻμ⊂ μ.≡.R_∗ʻʻμ⊂ μ
Dem.
⊢.*90·22·132.⊃⊢:Rʻʻμ⊂ μ. ≡.R_∗ʻʻμ⊂ μ. (1)
[*91·602] ≡.(Rₚₒ)_∗ʻʻμ⊂ μ.
[(1) Rₚₒ/R ] ≡.Rₚₒʻʻμ⊂ μ (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·71 -/
/- PM-VERBATIM-BEGIN PM1:✱91·711
✱91·711. ⊢:Rʻʻμ⊂ μ.⊃.Rₚₒʻʻμ=Rʻʻμ
Dem.
⊢.*91·71·52.*37·2. ⊃⊢:Hp.⊃.Rₚₒʻʻμ⊂ Rʻʻμ (1)
⊢.*91·502. ⊃⊢.Rʻʻμ⊂ Rₚₒʻʻμ (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·711 -/
/- PM-VERBATIM-BEGIN PM1:✱91·72
✱91·72. ⊢.Rʻʻ(α∪ Rₚₒʻʻα)=Rₚₒʻʻα
Dem.
⊢.*37·22·33.⊃⊢.Rʻʻ(α∪ Rₚₒʻʻα) =Rʻʻα∪ (R| Rₚₒ)ʻʻα
[*37·221] =(R⊍R| Rₚₒ)ʻʻα
[*91·57] =Rₚₒʻʻα.⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·72 -/
/- PM-VERBATIM-BEGIN PM1:✱91·721
✱91·721. ⊢.Řʻʻ(α∪ Řₚₒʻʻα)=Řₚₒʻʻα [✱91·72 Ř/R.✱91·53 ]
✱91·721. ⊢ . Řʻʻ(α∪Ř_poʻʻα)=Ř_poʻʻα
PM-VERBATIM-END PM1:✱91·721 -/
/- PM-VERBATIM-BEGIN PM1:✱91·73
✱91·73. ⊢:. P, Q∈ PotidʻR.P ≠ Q.⊃:(∃ T):T∈ PotʻR:Q=P| T.∨.P=Q| T
Dem.
⊢.*91·45.⊃
⊢:. Hp. ⊃:(∃ T):T∈ PotidʻR:Q=P| T.P| T ≠ P.∨.P=Q| T.Q| T ≠ Q (1)
⊢.*91·504.*50·62. ⊃⊢:P∈ PotidʻR.⊃.P| I↾ CʻR=P:
[Transp] ⊃⊢:P, T∈ PotidʻR.P| T ≠ P.⊃.T ≠ I↾ CʻR (2)
⊢.(1).(2).⊃
⊢:. Hp. ⊃:(∃ T):T∈ PotidʻR.T ≠ I↾ CʻR:Q=P| T.∨.P=Q| T (3)
⊢.*91·23. ⊃⊢:T∈ PotidʻR.T ≠ I↾ CʻR.⊃.T∈ PotʻR (4)
⊢.(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·73 -/
/- PM-VERBATIM-BEGIN PM1:✱91·731
✱91·731. ⊢:. P, Q∈ PotidʻR.P ≠ Q.⊃:(∃ T):T∈ PotʻR:Q=T| P.∨.P=T| Q [✱91·73·34]
✱91·731. ⊢ : P,Q∈PotidʻR . P≠Q .⊃: (∃T): T∈PotʻR : Q=T|P .∨. P=T|Q
PM-VERBATIM-END PM1:✱91·731 -/
/- PM-VERBATIM-BEGIN PM1:✱91·732
✱91·732. ⊢:. P,Q∈ PotidʻR. P ≠ Q.⊃: (∃ S):S∈ PotidʻR:Q = S| R| P.∨.P = S| R| Q
Dem.
⊢.*91·731·24.⊃
⊢:. Hp. ⊃:(∃ S,T):S∈ PotidʻR.T=S| R:Q = T| P.∨.P = T| Q:
[*13·195] ⊃:(∃ S):S∈ PotidʻR:Q = S| R| P.∨.P = S| R| Q:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·732 -/
/- PM-VERBATIM-BEGIN PM1:✱91·74
✱91·74. ⊢.ŘʻʻR⃖_∗ʻx = R⃖ₚₒʻx.RʻʻR⃗_∗ʻx = R⃗ₚₒʻx [✱91·52.✱37·302]
✱91·74. ⊢ . Řʻʻ←R_*ʻx=←R_poʻx . Rʻʻ→R_*ʻx=→R_poʻx
PM-VERBATIM-END PM1:✱91·74 -/
/- PM-VERBATIM-BEGIN PM1:✱91·75
✱91·75. ⊢.R_∗⊍Ř_∗ = R_∗⊍Řₚₒ = Rₚₒ⊍Ř_∗ = Rₚₒ⊍I↾ CʻR⊍Řₚₒ
Dem.
⊢.*50·5·51. ⊃⊢.Cnvʻ(I↾ CʻR) = I↾ CʻR.
[*91·54] ⊃⊢.Ř_∗ = I↾ CʻR⊍Řₚₒ. (1)
[*91·54.*23·56] ⊃⊢.R_∗⊍Ř_∗ = Rₚₒ⊍I↾ CʻR⊍Řₚₒ (2)
[*91·54] = R_∗⊍Řₚₒ (3)
[(1)] = Rₚₒ ⊍ Ř_∗ (4)
⊢.(2).(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱91·75 -/

/- PM-VERBATIM-BEGIN PM1:✱91·575
✱91·575. ⊢.Rₚₒ²=R| Rₚₒ=Rₚₒ| R=R²| R_∗=R_∗| R²=R| R_∗| R
PM-VERBATIM-END PM1:✱91·575 -/
