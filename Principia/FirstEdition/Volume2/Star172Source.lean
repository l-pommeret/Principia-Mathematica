/-! Principia Mathematica, first edition, volume II, ✱172.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱172·01
Π ʻP=M̂ N̂ {M,N∈ F_Δ ʻCʻP:. (∃ Q):(MʻQ)Q(NʻQ):RPQ.R≠ Q.⊃ _R.MʻR=NʻR} Df
PM-VERBATIM-END PM2:✱172·01 -/

/- PM-VERBATIM-BEGIN PM2:✱172·1
⊢ :: M (Π ʻP)N.≡ :. M,N∈ F_Δ ʻCʻP:. (∃ Q):(MʻQ)Q(NʻQ):RPQ.R≠ Q.⊃ _R.MʻR=NʻR [(*172·01)]
PM-VERBATIM-END PM2:✱172·1 -/

/- PM-VERBATIM-BEGIN PM2:✱172·11
⊢ :: M(Π ʻP)N.≡ :. M,N∈ F_Δ ʻCʻP:. (∃ Q):Q∈ CʻP.(MʻQ)Q(NʻQ):RPQ.R≠ Q.⊃ _R.MʻR=NʻR
PM-VERBATIM-END PM2:✱172·11 -/

/- PM-VERBATIM-BEGIN PM2:✱172·12
⊢ .CʻΠ ʻP⊂ F_Δ ʻCʻP
PM-VERBATIM-END PM2:✱172·12 -/

/- PM-VERBATIM-BEGIN PM2:✱172·13
⊢ .Π ʻΛ̇ =Λ̇
PM-VERBATIM-END PM2:✱172·13 -/

/- PM-VERBATIM-BEGIN PM2:✱172·14
⊢ :Λ̇ ∈ CʻP.⊃ .Π ʻP=Λ̇
PM-VERBATIM-END PM2:✱172·14 -/

/- PM-VERBATIM-BEGIN PM2:✱172·141
⊢ :. ∃̇ !Π ʻP.⊃ :Q∈ CʻP.⊃ _Q.∃̇ !Q [*172·14.Transp]
PM-VERBATIM-END PM2:✱172·141 -/

/- PM-VERBATIM-BEGIN PM2:✱172·15
⊢ :M∈ F_Δ ʻCʻP.Q∈ CʻP.(MʻQ)Qy.⊃ .M(Π ʻP){M↾ -ι ʻQ⊍ y↓ Q}
PM-VERBATIM-END PM2:✱172·15 -/

/- PM-VERBATIM-BEGIN PM2:✱172·151
⊢ :N∈ F_Δ ʻCʻP. Q∈ CʻP.yQ(NʻQ).⊃ . {N↾ -ι ʻQ⊍ y↓ Q}(Π ʻP)N [Proof as in *172·15]
PM-VERBATIM-END PM2:✱172·151 -/

/- PM-VERBATIM-BEGIN PM2:✱172·16
⊢ :M∈ F_Δ ʻCʻP.∃̇ !M-̇ B.⊃ .M∈ ᗡʻΠ ʻP
PM-VERBATIM-END PM2:✱172·16 -/

/- PM-VERBATIM-BEGIN PM2:✱172·161
⊢ :M∈ F_Δ ʻCʻP.∃̇ !M-̇ B| Cnv.⊃ .M∈ DʻΠ ʻP
PM-VERBATIM-END PM2:✱172·161 -/

/- PM-VERBATIM-BEGIN PM2:✱172·162
⊢ :∃̇ !P.⊃ .B⃗ʻΠ ʻP=B_Δ ʻCʻP.B⃗ʻCnvʻΠ ʻP=B_Δ ʻCnvʻʻCʻP
PM-VERBATIM-END PM2:✱172·162 -/

/- PM-VERBATIM-BEGIN PM2:✱172·17
⊢ :∃̇ !P.⊃ .CʻΠ ʻP=F_Δ ʻCʻP
PM-VERBATIM-END PM2:✱172·17 -/

/- PM-VERBATIM-BEGIN PM2:✱172·171
⊢ :∃̇ !P.⊃ . DʻΠ ʻP=F_Δ ʻCʻP-B_Δ ʻCnvʻʻCʻP. ᗡʻΠ ʻP=F_Δ ʻCʻP-B_Δ ʻCʻP [*172·162·17]
PM-VERBATIM-END PM2:✱172·171 -/

/- PM-VERBATIM-BEGIN PM2:✱172·18
⊢ :. ∃̇ !P.⊃ :∃̇ !Π ʻP.≡ .∃ !F_Δ ʻCʻP [*172·17]
PM-VERBATIM-END PM2:✱172·18 -/

/- PM-VERBATIM-BEGIN PM2:✱172·181
⊢ :. Mult ax.⊃ :Λ̇ ∼∈ CʻP.∃̇ !P.≡ .∃̇ !Π ʻP
PM-VERBATIM-END PM2:✱172·181 -/

/- PM-VERBATIM-BEGIN PM2:✱172·182
⊢ :: Mult ax.⊃ :. Λ̇ ∈ CʻP.∨.P=Λ̇ :≡ .Π ʻP=Λ̇ [*172·181.Transp]
PM-VERBATIM-END PM2:✱172·182 -/

/- PM-VERBATIM-BEGIN PM2:✱172·19
⊢ :∃̇ !Π ʻP.⊃ .ṡ ʻCʻΠ ʻP=F↾ CʻP [*172·17.*80·42]
PM-VERBATIM-END PM2:✱172·19 -/

/- PM-VERBATIM-BEGIN PM2:✱172·191
⊢ .ṡ ʻCʻΠ ʻP ⪽ F↾ CʻP
PM-VERBATIM-END PM2:✱172·191 -/

/- PM-VERBATIM-BEGIN PM2:✱172·192
⊢ .ᗡʻ(F↾ β )=β -ι ʻΛ̇
PM-VERBATIM-END PM2:✱172·192 -/

/- PM-VERBATIM-BEGIN PM2:✱172·2
⊢ .Π ʻ(P↓ P)=P↓_., P
PM-VERBATIM-END PM2:✱172·2 -/

/- PM-VERBATIM-BEGIN PM2:✱172·21
⊢ :P≠ Q.⊃ .P× Q=† (Q↓ P)^;Π ʻ(P↓ Q)
PM-VERBATIM-END PM2:✱172·21 -/

/- PM-VERBATIM-BEGIN PM2:✱172·22
⊢ :P≠ Q.⊃ .{† (Q↓ P)}↾ F_Δ ʻ(ι ʻP∪ ι ʻQ)∈ (P× Q) smor̅ Π ʻ(P↓ Q)
PM-VERBATIM-END PM2:✱172·22 -/

/- PM-VERBATIM-BEGIN PM2:✱172·23
⊢ :P≠ Q.⊃ .Π ʻ(P↓ Q) smor P× Q [*172·22]
PM-VERBATIM-END PM2:✱172·23 -/

/- PM-VERBATIM-BEGIN PM2:✱172·3
⊢ :. ∃̇ !P.Z∼∈ CʻP.⊃ :MΠ ʻ(P⇸ Z)N.≡ . (∃ S,T,u,v).(u↓ S)(Π ʻP× Z)(v↓ T).M=S⊍ u↓ Z.N=T⊍ v↓ Z
PM-VERBATIM-END PM2:✱172·3 -/

/- PM-VERBATIM-BEGIN PM2:✱172·31
⊢ :∃̇ !P.Z∼∈ CʻP. W=M̂ R̂ {(∃̇ S,u).S∈ F_Δ ʻCʻP.u∈ CʻZ.R=u↓ S.M=S⊍ u↓ Z}.⊃ . W∈ Π ʻ(P⇸ Z) smor̅ (Π ʻP x Z)
PM-VERBATIM-END PM2:✱172·31 -/

/- PM-VERBATIM-BEGIN PM2:✱172·32
⊢ :Z∼∈ CʻP.⊃ .Π ʻ(P⇸ Z) smor Π ʻP× Z
PM-VERBATIM-END PM2:✱172·32 -/

/- PM-VERBATIM-BEGIN PM2:✱172·321
⊢ :Z∼∈ CʻP.⊃ .Π ʻ(Z⇷CʻP) smor Z× Π ʻP [Proof by similar stages to those in proof of *172·32]
PM-VERBATIM-END PM2:✱172·321 -/

/- PM-VERBATIM-BEGIN PM2:✱172·33
⊢ ::∃̇ !P.∃̇ !Q.CʻP∩ CʻQ=Λ .⊃ :. M{Π ʻ(P⤉Q)}N. ≡ :(∃ S,T,S',T'):S,S'∈ F_Δ ʻCʻP.T,T'∈ F_Δ ʻCʻQ: S(Π ʻP)S'.∨.S=S'.T(Π ʻQ)Tʻ:M=S⊍ T.M'=S'⊍ T'
PM-VERBATIM-END PM2:✱172·33 -/

/- PM-VERBATIM-BEGIN PM2:✱172·34
⊢ :∃̇ !P.∃̇ !Q.CʻP∩ CʻQ =Λ .⊃ . (ṡ | C)∈ {Π ʻ(P⤉Q)} smor̅ {Π ʻP× Π ʻQ}
PM-VERBATIM-END PM2:✱172·34 -/

/- PM-VERBATIM-BEGIN PM2:✱172·35
⊢ :∃̇ !P.∃̇ !Q.CʻP∩ CʻQ=Λ .⊃ .Π ʻ(P⤉Q) smor Π ʻP× Π ʻQ [*172·34]
PM-VERBATIM-END PM2:✱172·35 -/

/- PM-VERBATIM-BEGIN PM2:✱172·36
⊢ :X≠ Y.X≠ Z.Y≠ Z.⊃ .Π ʻ(X↓ Y)⇸ ZsmorX× Y× Z
PM-VERBATIM-END PM2:✱172·36 -/

/- PM-VERBATIM-BEGIN PM2:✱172·361
⊢ :X≠ Y.X≠ Z.Y≠ Z.⊃ .Π ʻX⇷(Y↓ Z) smor X× Y× Z [Proof as in *172·36]
PM-VERBATIM-END PM2:✱172·361 -/

/- PM-VERBATIM-BEGIN PM2:✱172·37
⊢ :X≠ Y.X≠ Z. X≠ W.Y≠ Z.Y≠ W.Z≠ W.⊃ . Π ʻ{(X↓ Y)⤉(Z↓ W)} smor X× Y× Z× W
PM-VERBATIM-END PM2:✱172·37 -/

/- PM-VERBATIM-BEGIN PM2:✱172·4
⊢ :T∈ P smor smor̅ Q.⊃ .{T∥ CnvʻT† }↾ CʻΠ ʻQ∈ 1 arrow 1
PM-VERBATIM-END PM2:✱172·4 -/

/- PM-VERBATIM-BEGIN PM2:✱172·401
⊢ :T∈ P smor smor̅ Q.N∈ F_Δ ʻCʻQ. S∈ CʻQ.⊃ . {(T∥ CnvʻT† )ʻN}ʻT^;S=TʻNʻS
PM-VERBATIM-END PM2:✱172·401 -/

/- PM-VERBATIM-BEGIN PM2:✱172·402
⊢ :T∈ P smor smor̅ Q. N,N'∈ F_Δ ʻCʻQ.S∈ CʻQ.M=(T∥ CnvʻT† )ʻN. Mʻ=(T∥ CnvʻT† )ʻN'.R=T^;S.⊃ : NʻS=N'ʻS.≡ .MʻR=M'ʻR:(NʻS)S(N'ʻS).≡ .(MʻR)R(M'ʻR)
PM-VERBATIM-END PM2:✱172·402 -/

/- PM-VERBATIM-BEGIN PM2:✱172·403
⊢ :T∈ P smor smor̅ Q.⊃ .(T∥ CnvʻT† )ʻʻF_Δ ʻCʻQ⊂ F_Δ ʻCʻP
PM-VERBATIM-END PM2:✱172·403 -/

/- PM-VERBATIM-BEGIN PM2:✱172·404
⊢ :. T∈ P smor smor̅ Q.⊃ : N∈ F_Δ ʻCʻQ.M=T| N| CnvʻT† .≡ . M∈ F_Δ ʻCʻP.N=Ť | M| CnvʻŤ †
PM-VERBATIM-END PM2:✱172·404 -/

/- PM-VERBATIM-BEGIN PM2:✱172·41
⊢ :T∈ P smor smor̅ Q.⊃ .F_Δ ʻCʻP=(T∥ CnvʻT† )ʻʻF_Δ ʻCʻQ
PM-VERBATIM-END PM2:✱172·41 -/

/- PM-VERBATIM-BEGIN PM2:✱172·42
⊢ :T∈ P smor smor̅ Q.⊃ .(T| CnvʻT† )↾ CʻΠ ʻQ∈ (Π ʻP) smor̅ (Π ʻQ)
PM-VERBATIM-END PM2:✱172·42 -/

/- PM-VERBATIM-BEGIN PM2:✱172·421
⊢ :S=T↾ CʻΣ ʻQ.S ∈ P smor smor̅ Q.⊃ . (S∥ CnvʻS† )↾ F_Δ ʻCʻQ=(T∥ CnvʻT† )↾ F_Δ ʻCʻQ
PM-VERBATIM-END PM2:✱172·421 -/

/- PM-VERBATIM-BEGIN PM2:✱172·43
⊢ :T↾ CʻΣ ʻQ∈ P smor smor̅ Q.⊃ . (T∥ CnvʻT† )↾ CʻΠ ʻQ∈ (Π ʻP)smor̅ (Π ʻQ) [*172·42·421]
PM-VERBATIM-END PM2:✱172·43 -/

/- PM-VERBATIM-BEGIN PM2:✱172·44
⊢ :P sm smorQ.⊃ .Π ʻP smor Π ʻQ [*172·42]
PM-VERBATIM-END PM2:✱172·44 -/

/- PM-VERBATIM-BEGIN PM2:✱172·45
⊢ :. Mult ax.⊃ :P,Q∈ Rel²excl.∃ !P smor̅ Q∩ Rlʻsmor.⊃ . Π ʻPsmorΠ ʻQ [*164·44 . *172·44]
PM-VERBATIM-END PM2:✱172·45 -/

/- PM-VERBATIM-BEGIN PM2:✱172·5
⊢ :CʻP=CʻQ.P∩̇ J=Q∩̇ J.⊃ .Π ʻP=Π ʻQ
PM-VERBATIM-END PM2:✱172·5 -/

/- PM-VERBATIM-BEGIN PM2:✱172·51
⊢ .Π ʻP=Π ʻ(P⊍ I↾ CʻP) [*172·5]
PM-VERBATIM-END PM2:✱172·51 -/

/- PM-VERBATIM-BEGIN PM2:✱172·52
⊢ :. Q∈ ᗡʻP.⊃ _Q.(∃ R).RPQ.R≠ Q:⊃ .Π ʻP=Π ʻ(P∩̇ J)
PM-VERBATIM-END PM2:✱172·52 -/
