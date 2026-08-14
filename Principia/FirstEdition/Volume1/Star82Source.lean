/-! # Principia Mathematica I, ✱82 — source vocabulary -/
namespace PM.FirstEdition.Volume1.Star82Source

abbrev Rel (α : Sort u) := α → α → Prop
abbrev Set' (α : Sort u) := α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z
def cnv (R : Rel α) : Rel α := fun x y => R y x
def domain (R : Rel α) : Set' α := fun x => ∃ y, R x y
def image (R : Rel α) (s : Set' α) : Set' α := fun y => ∃ x, s x ∧ R x y
def restrict (R : Rel α) (s : Set' α) : Rel α := fun x y => R x y ∧ s y
def Functional (R : Rel α) : Prop := ∀ x y z, R x y → R x z → y = z
def Injective (R : Rel α) : Prop := Functional (cnv R)
def Delta (F : Rel α → Prop) (s : Set' α) (R : Rel α) : Prop :=
  F R ∧ ∀ x y, R x y → s y

end PM.FirstEdition.Volume1.Star82Source
/- PM-VERBATIM-BEGIN PM1:✱82·2
✱82·2. ⊢:M∈ P_Δʻκ.N∈ Q_Δʻλ.Qʻʻλ⊂ κ.⊃.M| N∈ (P| Q)_Δʻλ
PM-VERBATIM-END PM1:✱82·2 -/
/- PM-VERBATIM-BEGIN PM1:✱82·21
✱82·21. ⊢:Q↾ λ∈ 1→Cls.λ⊂ ᗡʻQ.⊃.Q_Δʻλ=ιʻQ↾ λ
PM-VERBATIM-END PM1:✱82·21 -/
/- PM-VERBATIM-BEGIN PM1:✱82·22
✱82·22. ⊢:Q↾ λ∈ 1→Cls.λ=Q̌ʻʻκ.M∈ P_Δʻκ.⊃.M| Q∈ (P| Q)_Δʻλ
PM-VERBATIM-END PM1:✱82·22 -/
/- PM-VERBATIM-BEGIN PM1:✱82·221
✱82·221. ⊢:Q↾ λ∈ 1→Cls.λ⊂ ᗡʻQ.M∈ P_ΔʻQʻʻλ.⊃.M| Q↾ λ∈ (P| Q)_Δʻλ
PM-VERBATIM-END PM1:✱82·221 -/
/- PM-VERBATIM-BEGIN PM1:✱82·23
✱82·23. ⊢:Q↾ λ∈ Cls→1.κ=Qʻʻλ.R∈ (P| Q)_Δʻλ.⊃.R| Q̌∈ P_Δʻκ
PM-VERBATIM-END PM1:✱82·23 -/
/- PM-VERBATIM-BEGIN PM1:✱82·231
✱82·231. ⊢:Q↾ λ∈ Cls→1.R∈ (P| Q)_Δʻλ.⊃.R| Q̌∈ P_ΔʻQʻʻλ.R=R| Q̌| Q↾ λ
PM-VERBATIM-END PM1:✱82·231 -/
/- PM-VERBATIM-BEGIN PM1:✱82·24
✱82·24. ⊢:Q↾ λ∈ 1→1.κ⊂ DʻQ.λ=Q̌ʻʻ κ.R∈ (P| Q)_Δʻλ.⊃. κ=Qʻʻλ.R| Q̌∈ P_Δʻκ.R=R| Q̌| Q
PM-VERBATIM-END PM1:✱82·24 -/
/- PM-VERBATIM-BEGIN PM1:✱82·241
✱82·241. ⊢:Q↾ λ∈ 1→1.λ∈ Dʻ(Q̌)_∈.R∈ (P| Q)_Δʻλ.⊃.R=R| Q̌| Q
PM-VERBATIM-END PM1:✱82·241 -/
/- PM-VERBATIM-BEGIN PM1:✱82·25
✱82·25. ⊢:Q↾ λ∈ 1→1.κ⊂ DʻQ.λ=Q̌ʻʻκ.R∈ (P| Q)_Δʻλ.⊃. (∃ M).M∈ P_Δʻκ.R=M| Q [*82·24.*10·24]
PM-VERBATIM-END PM1:✱82·25 -/
/- PM-VERBATIM-BEGIN PM1:✱82·251
✱82·251. ⊢:Q↾ λ∈ 1→1.R∈ (P| Q)_Δʻλ.⊃.(∃ M).M∈ P_ΔʻQʻʻλ.R=M| Q↾ λ [*82·231.*10·24]
PM-VERBATIM-END PM1:✱82·251 -/
/- PM-VERBATIM-BEGIN PM1:✱82·26
✱82·26. ⊢:. Q↾ λ ∈ 1→1.κ⊂ DʻQ.λ=Q̌ʻʻκ.⊃: R∈ (P| Q)_Δʻλ.≡.(∃ M).M∈ P_Δʻκ.R=M| Q [*82·22·25]
PM-VERBATIM-END PM1:✱82·26 -/
/- PM-VERBATIM-BEGIN PM1:✱82·261
✱82·261. ⊢:. Q↾ λ∈ 1→1.λ⊂ ᗡʻQ.⊃: R∈ (P| Q)_Δʻλ.≡.(∃ M).M∈ P_ΔʻQʻʻλ.R=M| Q↾ λ [*82·221·251]
PM-VERBATIM-END PM1:✱82·261 -/
/- PM-VERBATIM-BEGIN PM1:✱82·27
✱82·27. ⊢:Q↾ λ∈ 1→1.κ⊂ DʻQ.λ=Q̌ʻʻκ.⊃.(P| Q)_Δʻλ=| QʻʻP_Δʻκ [*82·26.*43·121.*37·6]
PM-VERBATIM-END PM1:✱82·27 -/
/- PM-VERBATIM-BEGIN PM1:✱82·271
✱82·271. ⊢:Q↾ λ∈ 1→1.λ⊂ ᗡʻQ.⊃.(P| Q)_Δʻλ=| (Q↾ λ)ʻʻP_ΔʻQʻʻλ [*82·261.*43·121.*37·6]
PM-VERBATIM-END PM1:✱82·271 -/
/- PM-VERBATIM-BEGIN PM1:✱82·272
✱82·272. ⊢:Q↾ λ∈ 1→1.λ∈ Dʻ(Q̌)_∈.⊃.(P| Q)_Δʻλ=| QʻʻP_ΔʻQʻʻλ
PM-VERBATIM-END PM1:✱82·272 -/
/- PM-VERBATIM-BEGIN PM1:✱82·28
✱82·28. ⊢:. κ↿ Q∈ 1→1.λ⊂ ᗡʻ Q.κ=Qʻʻλ.⊃: R∈ (P| Q)_Δʻλ.≡.(∃ M).M∈ P_Δʻκ.R=M| Q [*82·26.*74·26]
PM-VERBATIM-END PM1:✱82·28 -/
/- PM-VERBATIM-BEGIN PM1:✱82·29
✱82·29. ⊢:κ↿ Q∈ 1→1.λ⊂ ᗡʻQ.κ=Qʻʻλ.⊃.(P| Q)_Δʻλ=| QʻʻP_Δʻκ [*82·27.*74·26]
PM-VERBATIM-END PM1:✱82·29 -/
/- PM-VERBATIM-BEGIN PM1:✱82·291
✱82·291. ⊢:κ↿ Q∈ 1→1.κ∈ DʻQ_∈.⊃.(P| Q)_ΔʻQ̌ʻʻκ=| QʻʻP_Δʻκ [Proof as in *82·272]
PM-VERBATIM-END PM1:✱82·291 -/
/- PM-VERBATIM-BEGIN PM1:✱82·3
✱82·3. ⊢:M∈ P_ΔʻQʻʻλ.⊃.Dʻ(M| Q↾ λ)=DʻM
PM-VERBATIM-END PM1:✱82·3 -/
/- PM-VERBATIM-BEGIN PM1:✱82·31
✱82·31. ⊢:R∈ (P| Q)_Δʻλ.⊃.Dʻ(R| Q̌)=DʻR
PM-VERBATIM-END PM1:✱82·31 -/
/- PM-VERBATIM-BEGIN PM1:✱82·32
✱82·32. ⊢:Q↾ λ∈ 1→1.λ⊂ ᗡʻQ.⊃.Dʻʻ(P| Q)_Δʻλ=DʻʻP_ΔʻQʻʻλ
PM-VERBATIM-END PM1:✱82·32 -/
/- PM-VERBATIM-BEGIN PM1:✱82·33
✱82·33. ⊢:κ↿ Q∈ 1→1.κ∈ DʻQ_∈.⊃.Dʻʻ(P| Q)_ΔʻQ̌ʻʻκ=DʻʻP_Δʻκ
PM-VERBATIM-END PM1:✱82·33 -/
/- PM-VERBATIM-BEGIN PM1:✱82·4
✱82·4. ⊢:T∈ 1→Cls.Pʻʻλ⊂ ᗡʻT.⊃.T| ʻʻP_Δʻλ⊂ (T| P)_Δʻλ
PM-VERBATIM-END PM1:✱82·4 -/
/- PM-VERBATIM-BEGIN PM1:✱82·41
✱82·41. ⊢:T∈ Cls→1.M∈ (T| P)_Δʻλ.⊃.Ť| M∈ P_Δʻλ.M=T| Ť| M
PM-VERBATIM-END PM1:✱82·41 -/
/- PM-VERBATIM-BEGIN PM1:✱82·411
✱82·411. ⊢:T∈ Cls→1.⊃.(T| P)_Δʻλ⊂ T| ʻʻP_Δʻλ [*82·41]
PM-VERBATIM-END PM1:✱82·411 -/
/- PM-VERBATIM-BEGIN PM1:✱82·42
✱82·42. ⊢:T∈ 1→1.Pʻʻλ⊂ ᗡʻT.⊃.(T| P)_Δʻλ=T| ʻʻP_Δʻλ [*82·4·411]
PM-VERBATIM-END PM1:✱82·42 -/
/- PM-VERBATIM-BEGIN PM1:✱82·43
✱82·43. ⊢:T, Q↾ λ∈ 1→1.Pʻʻλ⊂ ᗡʻT.λ⊂ ᗡʻQ.κ=Qʻʻλ.⊃. (T| P↾ λ| Q̌)_Δʻκ=(T∥ Q̌)ʻʻP_Δʻλ
PM-VERBATIM-END PM1:✱82·43 -/
/- PM-VERBATIM-BEGIN PM1:✱82·45
✱82·45. ⊢:Q↾ λ∈ 1→1.λ⊂ ᗡʻQ.⊃.(P| Q)_Δʻλ sm P_ΔʻQʻʻλ
PM-VERBATIM-END PM1:✱82·45 -/
/- PM-VERBATIM-BEGIN PM1:✱82·5
✱82·5. ⊢:P↾ Qʻʻλ∈ Cls→1.Q↾ λ ∈ 1→1.λ⊂ ᗡʻQ.⊃. (P| Q)_Δʻλ sm DʻʻP_ΔʻQʻʻλ [*82·45.*81·21]
PM-VERBATIM-END PM1:✱82·5 -/
/- PM-VERBATIM-BEGIN PM1:✱82·51
✱82·51. ⊢:P↾ κ∈ Cls→1.κ↿ Q∈ 1→1.λ⊂ ᗡʻQ.κ=Qʻʻλ.⊃. (P| Q)_Δʻλ sm DʻʻP_Δʻκ [*82·5.*74·251]
PM-VERBATIM-END PM1:✱82·51 -/
/- PM-VERBATIM-BEGIN PM1:✱82·52
✱82·52. ⊢:P↾ κ∈ Cls→1.κ↿ Q∈ 1→1.κ∈ DʻQ_∈.⊃.(P| Q)_ΔʻQ̌ʻʻκ sm DʻʻP_Δʻκ
PM-VERBATIM-END PM1:✱82·52 -/
/- PM-VERBATIM-BEGIN PM1:✱82·53
✱82·53. ⊢: P↾ κ,R↾ κ∈ Cls→1.κ↿ Q∈ 1→1.κ∈ DʻQ_∈ .P⃗ʻʻκ=R⃗ʻʻκ.⊃. (P| Q)_ΔʻQ̌ʻʻκ sm (R| Q)_ΔʻQ̌ʻʻκ. Dʻʻ(P| Q)_ΔʻQ̌ʻʻκ=Dʻʻ(R| Q)_ΔʻQ̌ʻʻκ= μ̂{α∈ P⃗ʻʻκ.⊃_α.μ∩ α∈ 1:μ⊂ Pʻʻκ} =DʻʻP_Δʻκ=DʻʻR_Δʻκ
PM-VERBATIM-END PM1:✱82·53 -/
