/-! Principia Mathematica, first edition, volume II, ✱161.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱161·01
P⇸ x = P⊍ CʻP↑ ℩ʻx Df
PM-VERBATIM-END PM2:✱161·01 -/

/- PM-VERBATIM-BEGIN PM2:✱161·02
x⇷P = ℩ʻx↑ CʻP⊍ P Df
PM-VERBATIM-END PM2:✱161·02 -/

/- PM-VERBATIM-BEGIN PM2:✱161·1
⊢ .P⇸ x = P⊍ CʻP↑ ℩ʻx [(*161·01)]
PM-VERBATIM-END PM2:✱161·1 -/

/- PM-VERBATIM-BEGIN PM2:✱161·101
⊢ .x⇷P = ℩ʻx↑ CʻP⊍ P [(*161·02)]
PM-VERBATIM-END PM2:✱161·101 -/

/- PM-VERBATIM-BEGIN PM2:✱161·11
⊢ :. y(P⇸ x)z.≡ :yPz.∨.y∈ CʻP.z = x [*161·1]
PM-VERBATIM-END PM2:✱161·11 -/

/- PM-VERBATIM-BEGIN PM2:✱161·111
⊢ :. y(x⇷P)z.≡ :y=x.z∈ CʻP.∨.yPz [*161·101]
PM-VERBATIM-END PM2:✱161·111 -/

/- PM-VERBATIM-BEGIN PM2:✱161·12
⊢ .x⇷P=Cnvʻ(P̌ ⇸ x) [*161·1·101.*35·84.*33·22]
PM-VERBATIM-END PM2:✱161·12 -/

/- PM-VERBATIM-BEGIN PM2:✱161·13
⊢ .Dʻ(P⇸ x)=CʻP.ᗡʻ(x⇷P)=CʻP
PM-VERBATIM-END PM2:✱161·13 -/

/- PM-VERBATIM-BEGIN PM2:✱161·131
⊢ :∃̇ !P.⊃ .ᗡʻ(P⇸ x)=ᗡʻP∪ ι ʻx.Dʻ(x⇷P)=DʻP∪ ι ʻx [*35·86.*161·1]
PM-VERBATIM-END PM2:✱161·131 -/

/- PM-VERBATIM-BEGIN PM2:✱161·14
⊢ :∃̇ !P.⊃ .Cʻ(P⇸ x)=CʻP∪ ι ʻx=Cʻ(x⇷P) [*161·13·131]
PM-VERBATIM-END PM2:✱161·14 -/

/- PM-VERBATIM-BEGIN PM2:✱161·141
⊢ :∃̇ !P.⊃ .B⃗ʻ(P⇸ x)=B⃗ʻP-ι ʻx.B⃗ʻCnvʻ(P⇸ x)=ι ʻx-CʻP [*161·13·131.*93·101]
PM-VERBATIM-END PM2:✱161·141 -/

/- PM-VERBATIM-BEGIN PM2:✱161·15
⊢ :∃̇ !P.x∼∈ CʻP.⊃ . B⃗ʻ(P⇸ x)=B⃗ʻP.B⃗ʻCnvʻ(P⇸ x)=ι ʻx.Bʻ(x⇷P̌ )=x [*161·141]
PM-VERBATIM-END PM2:✱161·15 -/

/- PM-VERBATIM-BEGIN PM2:✱161·16
⊢ :x∼∈ CʻP.⊃ .(P⇸ x)⥏CʻP=(P⇸ x)⥏(-ι ʻx)=P [*161·1]
PM-VERBATIM-END PM2:✱161·16 -/

/- PM-VERBATIM-BEGIN PM2:✱161·161
⊢ :x∼∈ CʻP.⊃ .(x⇷P)⥏CʻP=(x⇷P)⥏(-ι ʻx)=P
PM-VERBATIM-END PM2:✱161·161 -/

/- PM-VERBATIM-BEGIN PM2:✱161·2
⊢ .Λ̇ ⇸ x=Λ̇ [*35·75·82.*161·1]
PM-VERBATIM-END PM2:✱161·2 -/

/- PM-VERBATIM-BEGIN PM2:✱161·201
⊢ .x⇷Λ̇ =Λ̇
PM-VERBATIM-END PM2:✱161·201 -/

/- PM-VERBATIM-BEGIN PM2:✱161·21
⊢ .(x↓ y)⇸ z=x↓ y⊍ x↓ z⊍ y↓ z
PM-VERBATIM-END PM2:✱161·21 -/

/- PM-VERBATIM-BEGIN PM2:✱161·211
⊢ .x⇷(y↓ z)=x↓ y⊍ x↓ z⊍ y↓ z=(x↓ y)⇸ z [Proof as in *161·21]
PM-VERBATIM-END PM2:✱161·211 -/

/- PM-VERBATIM-BEGIN PM2:✱161·212
P⇸ x⇸ y=(P⇸ x)⇸ y Df
PM-VERBATIM-END PM2:✱161·212 -/

/- PM-VERBATIM-BEGIN PM2:✱161·213
x⇷y⇷P=x⇷(y⇷P) Df
PM-VERBATIM-END PM2:✱161·213 -/

/- PM-VERBATIM-BEGIN PM2:✱161·22
⊢ :∃̇ !P.⊃ .(P⇸ x)⇸ y=P⤉(x↓ y)
PM-VERBATIM-END PM2:✱161·22 -/

/- PM-VERBATIM-BEGIN PM2:✱161·221
⊢ :∃̇ !P.⊃ .x⇷(y⇷P)=(x↓ y)⤉P
PM-VERBATIM-END PM2:✱161·221 -/

/- PM-VERBATIM-BEGIN PM2:✱161·23
⊢ :∃̇ !Q.⊃ .(P⤉Q)⇸ y=P⤉(Q⇸ y)
PM-VERBATIM-END PM2:✱161·23 -/

/- PM-VERBATIM-BEGIN PM2:✱161·231
⊢ :∃̇ !P.⊃ .x⇷(P⤉Q)=(x⇷P)⤉Q
PM-VERBATIM-END PM2:✱161·231 -/

/- PM-VERBATIM-BEGIN PM2:✱161·232
⊢ :∃̇ !P.∃̇ !Q.⊃ .P⤉(x⇷Q)=(P⇸ x)⤉Q
PM-VERBATIM-END PM2:✱161·232 -/

/- PM-VERBATIM-BEGIN PM2:✱161·24
⊢ .x⇷(P⇸ y)=(x⇷P)⇸ y
PM-VERBATIM-END PM2:✱161·24 -/

/- PM-VERBATIM-BEGIN PM2:✱161·25
⊢ :∃̇ !P.∃̇ !Q.⊃ .(P ⇸ x) ⤉ (y ⇷ Q) = P ⤉ (x↓ y) ⤉ Q
PM-VERBATIM-END PM2:✱161·25 -/

/- PM-VERBATIM-BEGIN PM2:✱161·26
⊢ . x ⇷ {y ⇷ (z↓ w)} = (x↓ y) ⤉ (z↓ w) = {(x↓ y) ⇸ z} ⇸ w = {x ⇷ (y↓ z)} ⇸ w
PM-VERBATIM-END PM2:✱161·26 -/

/- PM-VERBATIM-BEGIN PM2:✱161·3
⊢ : ∃̇ !Q . S∈ P smor̅ Q . x∼∈ CʻP . y∼∈ CʻQ. ⊃ . S ⊍ x↓ y∈ (P ⇸ x) smor̅ (Q ⇸ y)
PM-VERBATIM-END PM2:✱161·3 -/

/- PM-VERBATIM-BEGIN PM2:✱161·301
⊢ : ∃̇ !Q. S∈ P smor̅ Q. x∼∈ CʻP. y∼∈ CʻQ. ⊃ . x↓ y ⊍ S∈ (x ⇷ P) smor̅ (y ⇷ Q)
PM-VERBATIM-END PM2:✱161·301 -/

/- PM-VERBATIM-BEGIN PM2:✱161·31
⊢ : P smor Q. x∼∈ CʻP. y∼∈ CʻQ. ⊃ . P ⇸ x smor Q ⇸ y. x ⇷ P smor y ⇷ Q
PM-VERBATIM-END PM2:✱161·31 -/

/- PM-VERBATIM-BEGIN PM2:✱161·32
⊢ : ∃̇ !Q. x∼∈ CʻP. y∼∈ CʻQ. S∈ (P ⇸ x) smor̅ (Q ⇸ y). ⊃ . S↾ (-ι ʻy)∈ P smor̅ Q. xSy
PM-VERBATIM-END PM2:✱161·32 -/

/- PM-VERBATIM-BEGIN PM2:✱161·321
⊢ : ∃̇ !Q. x∼∈ CʻP. y∼∈ CʻQ. S∈ (x ⇷ P) smor̅ (y ⇷ Q). ⊃ . S↾ (-ι ʻy)∈ P smor̅ Q. xSy
PM-VERBATIM-END PM2:✱161·321 -/

/- PM-VERBATIM-BEGIN PM2:✱161·33
⊢ :. x ∼∈ CʻP. y∼∈ CʻQ. ⊃ : P smor Q. ≡ . (P ⇸ x) smor (Q ⇸ y). ≡ . (x ⇷ P) smor (y ⇷ Q) [*161·31·32·321·2·201. *153·101]
PM-VERBATIM-END PM2:✱161·33 -/

/- PM-VERBATIM-BEGIN PM2:✱161·4
⊢ : CʻQ ⊂ ᗡʻS. x∈ ᗡʻS. S∈ 1 arrow Cls. ⊃ . S^;(Q ⇸ x) = S^;Q ⇸ Sʻx
PM-VERBATIM-END PM2:✱161·4 -/

/- PM-VERBATIM-BEGIN PM2:✱161·41
⊢ : CʻQ ⊂ ᗡʻS. x∈ ᗡʻS. S∈ 1 arrow Cls. ⊃ . S^;(x ⇷ Q) = Sʻx ⇷ S^;Q
PM-VERBATIM-END PM2:✱161·41 -/

/- PM-VERBATIM-BEGIN PM2:✱161·42
⊢ . ↓ y^;(Q ⇸ x) = ↓ y^;Q ⇸ (x↓ y) [*161·4.*55·21.*72·184]
PM-VERBATIM-END PM2:✱161·42 -/

/- PM-VERBATIM-BEGIN PM2:✱161·43
⊢ . ↓ y^;(x ⇷ Q) = (x↓ y) ⇷ y^;Q
PM-VERBATIM-END PM2:✱161·43 -/
