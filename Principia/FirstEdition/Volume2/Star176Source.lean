/-! Principia Mathematica, first edition, volume II, ✱176.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱176·01
P exp Q = ProdʻP↓_., ^;Q Df
PM-VERBATIM-END PM2:✱176·01 -/

/- PM-VERBATIM-BEGIN PM2:✱176·02
P^Q = ṡ ^;(P exp Q) Df
PM-VERBATIM-END PM2:✱176·02 -/

/- PM-VERBATIM-BEGIN PM2:✱176·1
⊢ . P exp Q = ProdʻP↓_., ^;Q = D^;Π ʻP↓_., ^;Q [(*176·01)]
PM-VERBATIM-END PM2:✱176·1 -/

/- PM-VERBATIM-BEGIN PM2:✱176·11
⊢ . P^Q = ṡ ^;(P exp Q) = ṡ ^;ProdʻP↓_., ^;Q = ṡ ^;D^;Π ʻP↓_., ^;Q [(*176·02)]
PM-VERBATIM-END PM2:✱176·11 -/

/- PM-VERBATIM-BEGIN PM2:✱176·12
⊢ :: μ (P exp Q) ν . ≡ :. μ , ν ∈ (CʻP) exp (CʻQ) :. (∃ y, x, x') : x ↓ y ∈ μ . x' ↓ y ∈ ν . xPx' : zQy . z ≠ y . w ↓ z ∈ μ . ⊃ w, z . w ↓ z ∈ ν
PM-VERBATIM-END PM2:✱176·12 -/

/- PM-VERBATIM-BEGIN PM2:✱176·13
⊢ : ∃̇ ! (P exp Q) . ≡ . ∃̇ ! P^Q . ≡ . ∃̇ ! Π ʻP↓_., ^;Q [*150·25 . *176·1·11]
PM-VERBATIM-END PM2:✱176·13 -/

/- PM-VERBATIM-BEGIN PM2:✱176·131
⊢ : Q = Λ̇ . ⊃ . P exp Q = Λ̇ . P^Q = Λ̇ [*165·241 . *173·2 . *150·42]
PM-VERBATIM-END PM2:✱176·131 -/

/- PM-VERBATIM-BEGIN PM2:✱176·132
⊢ : P = Λ̇ . ∃̇ ! Q . ⊃ . P exp Q = Λ̇ . P^Q = Λ̇ [*165·244 . *172·14 . *176·13 . *150·42]
PM-VERBATIM-END PM2:✱176·132 -/

/- PM-VERBATIM-BEGIN PM2:✱176·133
⊢ . CʻP^Q = ṡ ʻʻCʻ(P exp Q) [*176·11 . *150·22]
PM-VERBATIM-END PM2:✱176·133 -/

/- PM-VERBATIM-BEGIN PM2:✱176·14
⊢ : ∃̇ ! Q . ⊃ . Cʻ(P exp Q) = (CʻP) exp (CʻQ) . CʻP^Q = (CʻP ↑ CʻQ)_Δ ʻCʻQ
PM-VERBATIM-END PM2:✱176·14 -/

/- PM-VERBATIM-BEGIN PM2:✱176·15
⊢ : ∃̇ ! P . ∃̇ ! Q . ≡ . ∃̇ ! (P exp Q) . ≡ . ∃̇ ! P^Q
PM-VERBATIM-END PM2:✱176·15 -/

/- PM-VERBATIM-BEGIN PM2:✱176·151
⊢ :. P = Λ̇ .∨.Q = Λ̇ :≡ .P exp Q = Λ̇ . ≡ . P^Q = Λ̇ [*176·15]
PM-VERBATIM-END PM2:✱176·151 -/

/- PM-VERBATIM-BEGIN PM2:✱176·16
⊢ . Cʻ(P exp Q) ⊂ (CʻP) exp (CʻQ) . CʻP^Q ⊂ (CʻP ↑ CʻQ)_Δ ʻCʻQ [*176·14·151]
PM-VERBATIM-END PM2:✱176·16 -/

/- PM-VERBATIM-BEGIN PM2:✱176·18
⊢ . ṡ ↾ Cʻ(P exp Q) ∈ (P^Q) smor̅ (P exp Q)
PM-VERBATIM-END PM2:✱176·18 -/

/- PM-VERBATIM-BEGIN PM2:✱176·181
⊢ . P^Q smor (P exp Q) [*176·18]
PM-VERBATIM-END PM2:✱176·181 -/

/- PM-VERBATIM-BEGIN PM2:✱176·182
⊢ . (P exp Q) smor (Π ʻP ↓_., ^;Q) [*176·1 . *173·16 . *165·21]
PM-VERBATIM-END PM2:✱176·182 -/

/- PM-VERBATIM-BEGIN PM2:✱176·19
⊢ :: S(P^Q) T . ≡ :. S, T ∈ (CʻP ↑ CʻQ)_Δ ʻCʻQ :. (∃ y) : y ∈ CʻQ . (Sʻy) P (Tʻy) : y'Qy . y' ≠ y . ⊃ yʻ . Sʻy' = Tʻy'
PM-VERBATIM-END PM2:✱176·19 -/

/- PM-VERBATIM-BEGIN PM2:✱176·2
⊢ : U ↾ CʻR ∈ P smor̅ R . W ↾ CʻS ∈ Q smor̅ S . ⊃ . (U ∥ W̌ )_∈ ↾ Cʻ(R exp S) ∈ (P exp Q) smor̅ (R exp S)
PM-VERBATIM-END PM2:✱176·2 -/

/- PM-VERBATIM-BEGIN PM2:✱176·21
⊢ : U ↾ CʻR ∈ P smor̅ R . W ↾ CʻS ∈ Q smor̅ S . ⊃ . (U ∥ W̌ ) ↾ Cʻ(R^S) ∈ (P^Q) smor̅ (R^S)
PM-VERBATIM-END PM2:✱176·21 -/

/- PM-VERBATIM-BEGIN PM2:✱176·22
⊢ : P smor R . Q smor S . ⊃ . (P exp Q) smor (P exp S) . P^Q smor R^S [*176·2·21]
PM-VERBATIM-END PM2:✱176·22 -/

/- PM-VERBATIM-BEGIN PM2:✱176·23
⊢ : R smor smor P ↓_., ^;Q . ⊃ . Π ʻR smor (P exp Q)
PM-VERBATIM-END PM2:✱176·23 -/

/- PM-VERBATIM-BEGIN PM2:✱176·24
⊢ :. Mult ax . ⊃ : R ∈ Rel²excl ∩ NrʻQ . CʻR ⊂ NrʻP . ⊃ . Π ʻP smor (P exp Q) [*165·38 . *176·23]
PM-VERBATIM-END PM2:✱176·24 -/

/- PM-VERBATIM-BEGIN PM2:✱176·3
⊢ . Cnvʻ(P^Q) = (P̌ )^Q
PM-VERBATIM-END PM2:✱176·3 -/

/- PM-VERBATIM-BEGIN PM2:✱176·31
⊢ : ∃̇ ! Q . ⊃ . B⃗ʻ(P exp Q) = (B⃗ʻP) exp (CʻQ)
PM-VERBATIM-END PM2:✱176·31 -/

/- PM-VERBATIM-BEGIN PM2:✱176·311
⊢ : ∃̇ ! Q . ⊃ . B⃗ʻCnvʻ(P exp Q) = (B⃗ʻP) exp (CʻQ) [Proof as in *176·31]
PM-VERBATIM-END PM2:✱176·311 -/

/- PM-VERBATIM-BEGIN PM2:✱176·32
⊢ :∃̇ !Q.⊃ .B⃗ʻ(P^Q)=(B⃗ʻP↑ CʻQ)_Δ ʻCʻQ
PM-VERBATIM-END PM2:✱176·32 -/

/- PM-VERBATIM-BEGIN PM2:✱176·321
⊢ :∃̇ !Q.⊃ .B⃗ʻCnvʻ(P^Q)=(B⃗ʻP̌ ↑ CʻQ)_Δ ʻCʻQ [*176·32·3]
PM-VERBATIM-END PM2:✱176·321 -/

/- PM-VERBATIM-BEGIN PM2:✱176·33
⊢ :. ∃̇ !Q.⊃ : ∃ !B⃗ʻ(P exp Q).≡ .∃ !B⃗ʻ(P^Q).≡ .∃ !B⃗ʻP: ∃ !B⃗ʻCnvʻ(P exp Q).≡ .∃ !B⃗ʻCnvʻ(P^Q).≡ .∃ !B⃗ʻP̌ [*176·31·311·32·321.*116·18·15]
PM-VERBATIM-END PM2:✱176·33 -/

/- PM-VERBATIM-BEGIN PM2:✱176·34
⊢ :∃̇ !Q.E! BʻP.⊃ . Bʻ(P exp Q)=(BʻP)↓ʻʻCʻQ.Bʻ(P^Q)=(ι ʻBʻP)↑ CʻQ
PM-VERBATIM-END PM2:✱176·34 -/

/- PM-VERBATIM-BEGIN PM2:✱176·341
⊢ :∃̇ !Q.E! BʻP̌ .⊃ . BʻCnvʻ(P exp Q)=(BʻP̌ )↓ʻʻCʻQ.BʻCnvʻ(P^Q)=(ι ʻBʻP̌ )↑ CʻQ [Proof as in *176·34]
PM-VERBATIM-END PM2:✱176·341 -/

/- PM-VERBATIM-BEGIN PM2:✱176·35
⊢ :P ⪽ Q.⊃ .P^R ⪽ Q^R
PM-VERBATIM-END PM2:✱176·35 -/

/- PM-VERBATIM-BEGIN PM2:✱176·4
⊢ :∃̇ !Q.∃̇ !R.PʻʻCʻQ∩ PʻʻCʻR=Λ.CʻQ∪ CʻR⊂ ᗡʻP.⊃ . ṡ | C↾ Cʻ{(Π ʻP^;Q)× (Π ʻP^;R)}∈ {Π ʻP^;(Q⤉R)} smor̅ {(Π ʻP^;Q)× (Π ʻP^;R)}
PM-VERBATIM-END PM2:✱176·4 -/

/- PM-VERBATIM-BEGIN PM2:✱176·41
⊢ :∃̇ !Q.∃̇ !R. PʻʻCʻQ∩ PʻʻCʻR=Λ.CʻQ∪ CʻR⊂ ᗡʻP.⊃ . Π ʻP^;(Q⤉R) smor (Π ʻP^;Q)× (Π ʻP^;R) [*176·4]
PM-VERBATIM-END PM2:✱176·41 -/

/- PM-VERBATIM-BEGIN PM2:✱176·42
⊢ :∃̇ !Q.∃̇ !R.CʻQ∩ CʻR=Λ.⊃ .P^Q× P^R smor P^Q⤉R. (P exp Q)× (P exp R) smor P exp (Q⤉R)
PM-VERBATIM-END PM2:✱176·42 -/

/- PM-VERBATIM-BEGIN PM2:✱176·43
⊢ :S∈ Rel²excl.S ⪽ J.⊃ . s↾ CʻProdʻ(P exp )^;S∈ P exp (Σ ʻS) smor̅ Prodʻ(P exp )^;S
PM-VERBATIM-END PM2:✱176·43 -/

/- PM-VERBATIM-BEGIN PM2:✱176·44
⊢ :S∈ Rel²excl.S ⪽ J.⊃ .{Prodʻ(P exp )^;S} smor {P exp (Σ ʻS)} [*176·43]
PM-VERBATIM-END PM2:✱176·44 -/

/- PM-VERBATIM-BEGIN PM2:✱176·5
⊢ :. M↾ CʻR∈ 1 arrow 1.CʻR⊂ ᗡʻM.CʻQ⊂ pʻᗡʻʻʻMʻʻCʻR. MʻʻCʻR⊂ 1 arrow 1:z,z'∈ CʻR.∃ !DʻMʻz∩ DʻMʻz'.⊃ z,z'.z=z': T=x̂ X̂ {(∃ u,z).u∈ CʻQ.z∈ CʻR.x=(Mʻz)ʻu.X=u↓ (Mʻz)}: ⊃ .T∈ 1 arrow 1
PM-VERBATIM-END PM2:✱176·5 -/

/- PM-VERBATIM-BEGIN PM2:✱176·501
⊢ :Hp*176·5.⊃ .ᗡʻT=CʻΣ ʻQ↓_., ^;M^;R
PM-VERBATIM-END PM2:✱176·501 -/

/- PM-VERBATIM-BEGIN PM2:✱176·502
⊢ :Hp*176·5.z∈ CʻR.⊃ .T^;Q↓_., ʻMʻz=† QʻMʻz
PM-VERBATIM-END PM2:✱176·502 -/

/- PM-VERBATIM-BEGIN PM2:✱176·503
⊢ :Hp*176·5.⊃ .T∈ († Q^;M^;R) smor smor̅ (Q↓_., ^;M^;R)
PM-VERBATIM-END PM2:✱176·503 -/

/- PM-VERBATIM-BEGIN PM2:✱176·51
⊢ :. M↾ CʻR∈ 1 arrow 1.MʻʻCʻR⊂ 1 arrow 1. CʻR⊂ ᗡʻM.CʻQ⊂ pʻᗡʻʻMʻʻCʻR: z,z'∈ CʻR.∃ !DʻMʻz∩ DʻMʻz'.⊃ z,z'.z=z':⊃ .† Q^;M^;R smor smorQ↓_., ^;R
PM-VERBATIM-END PM2:✱176·51 -/

/- PM-VERBATIM-BEGIN PM2:✱176·52
⊢ :. z∈ CʻR.⊃ z.Mʻz∈ (Pʻz) smor̅ Q:⊃ .P^;R=† Q^;M^;R
PM-VERBATIM-END PM2:✱176·52 -/

/- PM-VERBATIM-BEGIN PM2:✱176·53
⊢ :. M↾ CʻR∈ 1 arrow 1:z∈ CʻR.⊃ z.Mʻz∈ (Pʻz) smor̅ Q: z,z'∈ CʻR.∃ !CʻPʻz∩ CʻPʻz'.⊃ z,z'.z=z':⊃ .P^;R smor smor Q↓_., ^;R
PM-VERBATIM-END PM2:✱176·53 -/

/- PM-VERBATIM-BEGIN PM2:✱176·54
⊢ :. ∃̇ !P.∃̇ !Q.M=Ẑ ẑ [z∈ CʻR.Z={| (Cnvʻ↓ z)}_∈ ↾ Cʻ(P exp Q)].⊃ : M∈ 1 arrow 1:z∈ CʻR.⊃ z.Mʻz∈ (ProdʻP↓_., ^;Q↓_., z) smor̅ (ProdʻP↓_., ^;Q)
PM-VERBATIM-END PM2:✱176·54 -/

/- PM-VERBATIM-BEGIN PM2:✱176·541
⊢ .(P↓_., )† ^;Q↓_., ^;R∈ Rel³arithm.Σ ʻ(P↓_., )† ^;Q↓_., ^;R=P↓_., ^;Σ ʻQ↓_., ^;R
PM-VERBATIM-END PM2:✱176·541 -/

/- PM-VERBATIM-BEGIN PM2:✱176·55
⊢ :∃̇ !P.∃̇ !Q.⊃ .Prod^;(P↓_., )† ^;Q↓_., ^;R smor smor (ProdʻP↓_., ^;Q)↓_., ^;R
PM-VERBATIM-END PM2:✱176·55 -/

/- PM-VERBATIM-BEGIN PM2:✱176·56
⊢ :∃̇ !P.∃̇ ! Q.R ⪽ J.⊃ . ProdʻΣ ʻ(P↓_., )† ^;Q↓_., ^;R smor Prodʻ(ProdʻP↓_., ^;Q)↓_., ^;R
PM-VERBATIM-END PM2:✱176·56 -/

/- PM-VERBATIM-BEGIN PM2:✱176·57
⊢ :R ⪽ J.⊃ .{(P exp Q) exp R} smor {P exp (R× Q)}.(P^Q)^R smor P^R× Q
PM-VERBATIM-END PM2:✱176·57 -/
