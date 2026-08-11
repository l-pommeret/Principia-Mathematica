/-
  Source-only opening of PM III ✱250.  These are archival transcriptions,
  not Lean declarations, targets, or derivations.
-/

/- PM-VERBATIM-BEGIN PM3:STAR250-SUMMARY-P4
✱250.  ELEMENTARY PROPERTIES OF WELL-ORDERED SERIES.

Summary of ✱250.

A relation is called “well-ordered” when every existent sub-class of its
field has one or more minima.  A well-ordered series is defined as a
well-ordered relation which is a series.  We shall denote the class of
well-ordered relations by “Bord,” which is an abbreviation for “bene ordinata”
or “bien ordonnée.”  The class of well-ordered series will be denoted by Ω.
Thus our definitions are

  Bord = P̂ (Cl exʻCʻP ⊂ ∃ʻminₚ)  Df,
  Ω = Ser ∩ Bord  Df.

Well-ordered relations other than series will be seldom referred to after the
present number.

By applying the definition of “Bord” to unit classes, it appears that a
well-ordered relation must be contained in diversity (✱250·104).  A
well-ordered relation is one whose existent upper sections all have minima
(✱250·102).  Hence by ✱211·17,

✱250·103.  ⊢ : P ∈ Bord .≡ . Pₚₒ ∈ Bord

Hence by ✱250·104,

✱250·106.  ⊢ : P ∈ Bord .⊃ . Pₚₒ ⊂ J

By considering couples, it can be shown (✱250·111) that a well-ordered
relation in which no class has more than one minimum is connected; hence by
✱204·16 and ✱250·105, it is a series.  Thus we have

✱250·125.  ⊢ : P ∈ Ω .≡ . E!! minₚʻʻCl exʻCʻP,

I.e. a well-ordered series is a relation such that every existent sub-class of
the field has a unique minimum.  This might have been taken as the definition
of Ω.

By the definition of Ω we have

✱250·121.  ⊢ :: P ∈ Ω .≡ : P ∈ Ser : α ⊂ CʻP . ∃! α .⊃ₐ . E! minₚʻα :
  ≡ : P ∈ Ser : ∃! α ∩ CʻP .⊃ₐ . E! minₚʻα

Applying this to CʻP we have

✱250·13.  ⊢ : P ∈ Ω − ιʻΛ .⊃ . E! BʻP
PM-VERBATIM-END PM3:STAR250-SUMMARY-P4 -/

/- PM-VERBATIM-BEGIN PM3:STAR250-SUMMARY-P5
✱250·141.  ⊢ : P ∈ Ω .⊃ . P ▷ α ∈ Ω

✱250·17.  ⊢ :: P, Q ∈ Ω − ιʻΛ .⊃ : P smor Q .≡ . P ▷ ∃ʻP smor Q ▷ ∃ʻQ

This proposition justifies the subtraction of ι from the beginning, and is
useful in the theory of segments of well-ordered series.

We have next (✱250·2—·243) an important set of propositions on P₁ when
P ∈ Ω.  The most useful of these is

✱250·21.  ⊢ : P ∈ Ω .⊃ . DʻP = DʻP₁

I.e. in a well-ordered series every term except the last (if any) has an
immediate successor.  (It is not in general the case that every term except
the first has an immediate predecessor.)  Another useful proposition is

✱250·242.  ⊢ : P ∈ Ω .⊃ . P = P₁ ∪ P₁ | P

The next set of propositions (✱250·3—·362) is concerned with “transfinite
induction.”  We have

✱250·33.  ⊢ . Ω = connex ∩ P̂ {α ⊂ CʻP ∩ σ .⊃ₐ . seqₚʻα ⊂ σ : ⊃ₐ . CʻP ⊂ σ}

I.e. a well-ordered series is a connected relation P such that the whole field
of P is contained in every class σ which is such that the sequent (if any) of
every sub-class of CʻP ∩ σ is a member of σ.

✱250·35.  ⊢ . Bord = P̂ {x ∈ CʻP . P⃗ʻx ⊂ σ .⊃ₓ . x ∈ σ : ⊃ₐ . CʻP ⊂ σ}

I.e. a well-ordered relation is a relation P whose field is contained in every
class σ which contains every member of CʻP whose predecessors are all
contained in σ.  We may say that a property is “transfinitely hereditary” in
P if it belongs to the sequents of all classes composed of members of CʻP
which possess the property.  In virtue of ✱250·33, if P is well-ordered,
every transfinitely hereditary property belongs to every member of CʻP, and
conversely.

Our next set of propositions (✱250·4—·44) is concerned with Λ and couples.
We prove that Λ ∈ Ω (✱250·4) and that x ≠ y .⊃ . x ↓ y ∈ Ω (✱250·41).

✱250·5—·54 are concerned with selections.  We have

✱250·5.  ⊢ : P ∈ Ω .⊃ . minₚ ▷ Cl exʻCʻP ∈ εₐʻCl exʻCʻP . ιʻCʻP = ProdʻCl exʻCʻP

whence

✱250·51.  ⊢ : α ∈ CʻʻΩ .⊃ . ∃! εₐʻCl exʻα

Observe that CʻʻΩ is the class of those classes that can be well-ordered.
From ✱250·51 we deduce

✱250·54.  ⊢ : CʻʻΩ ∪ 1 ≡ Cls .⊃ . Mult ax

The converse, which is Zermelo’s theorem, is proved in ✱258.
PM-VERBATIM-END PM3:STAR250-SUMMARY-P5 -/

/- PM-VERBATIM-BEGIN PM3:✱250·01
✱250·01.  Bord = P̂ (Cl exʻCʻP ⊂ ∃ʻminₚ)  Df
PM-VERBATIM-END PM3:✱250·01 -/

/- PM-VERBATIM-BEGIN PM3:✱250·02
✱250·02.  Ω = Ser ∩ Bord  Df
PM-VERBATIM-END PM3:✱250·02 -/

/- PM-VERBATIM-BEGIN PM3:✱250·1
✱250·1.  ⊢ : P ∈ Bord .≡ . Cl exʻCʻP ⊂ ∃ʻminₚ  [(*250·01)]
PM-VERBATIM-END PM3:✱250·1 -/

/- PM-VERBATIM-BEGIN PM3:✱250·101
✱250·101.  ⊢ :: P ∈ Bord .≡ : ∃! α ∩ CʻP .⊃ₐ . ∃! minₚʻα  [✱250·1 . ✱205·15]
PM-VERBATIM-END PM3:✱250·101 -/

/- PM-VERBATIM-BEGIN PM3:✱250·102
✱250·102.  ⊢ : P ∈ Bord .≡ . sectʻP − ιʻΛ ⊂ ∃ʻminₚ

Dem.
  ⊢ . ✱250·1 .⊃ ⊢ : P ∈ Bord .⊃ . sectʻP − ιʻΛ ⊂ ∃ʻminₚ  (1)
  ⊢ . ✱205·19 .⊃ ⊢ . min (Pₚₒ)ʻα = min (Pₚₒ)ʻP⁎ʻα  [✱205·68]  (2)
  ⊢ . ✱90·331 . ✱211·13 .⊃ ⊢ : ∃! α ∩ CʻP .⊃ . P⁎ʻʻα ∈ sectʻP − ιʻΛ  (3)
  ⊢ . (3) .⊃ ⊢ :: sectʻP − ιʻΛ ⊂ ∃ʻminₚ .⊃ : ∃! α ∩ CʻP .⊃ . ∃! minₚʻ(P⁎ʻʻα)
      .⊃ . ∃! min (Pₚₒ)ʻα .⊃ . ∃! minₚʻα  (4)
      [✱205·26] [✱250·101]
  ⊢ . (1) . (4) .⊃ ⊢ . Prop
PM-VERBATIM-END PM3:✱250·102 -/

/- PM-VERBATIM-BEGIN PM3:✱250·103
✱250·103.  ⊢ : P ∈ Bord .≡ . Pₚₒ ∈ Bord  [✱250·102 . ✱211·17]
PM-VERBATIM-END PM3:✱250·103 -/

/- PM-VERBATIM-BEGIN PM3:✱250·104
✱250·104.  ⊢ . Bord ⊂ RlʻJ

Dem.
  ⊢ . ✱250·1 .⊃ ⊢ : P ∈ Bord . x ∈ CʻP .⊃ . x ∈ minₚʻιʻx  [✱205·194]
      .⊃ . ∼(xPx) : ⊃ ⊢ . Prop
PM-VERBATIM-END PM3:✱250·104 -/

/- PM-VERBATIM-BEGIN PM3:✱250·105
✱250·105.  ⊢ : P ∈ Bord .⊃ . Pₚₒ ⊂ J  [✱250·103·104]
PM-VERBATIM-END PM3:✱250·105 -/

/- PM-VERBATIM-BEGIN PM3:✱250·11
✱250·11.  ⊢ :: P ∈ connex .⊃ :: P ∈ Bord .≡ : ∃! α ∩ CʻP .⊃ₐ . E! minₚʻα :
  ≡ : α ⊂ CʻP . ∃! α .⊃ₐ . E! minₚʻα  [✱250·1·101 . ✱205·32]
PM-VERBATIM-END PM3:✱250·11 -/

/- PM-VERBATIM-BEGIN PM3:✱250·111
✱250·111.  ⊢ :: P ∈ Bord .⊃ : P ∈ connex .≡ . minₚ ∈ 1 → Cls

Dem. (continues on printed p. 7)
  ⊢ . ✱250·1 . ✱71·1 .⊃ ⊢ :: P ∈ Bord . minₚ ∈ 1 → Cls .⊃ :: x, y ∈ CʻP .⊃ :
    (ιʻx ∪ ιʻy) − P⁎ʻʻ(ιʻx ∪ ιʻy) ∈ 1  [✱54·4]  (1)
PM-VERBATIM-END PM3:✱250·111 -/

/- PM-VERBATIM-BEGIN PM3:✱250·112
✱250·112.  ⊢ : P ∈ connex ∩ Bord .≡ . E!! minₚʻʻCl exʻCʻP
PM-VERBATIM-END PM3:✱250·112 -/

/- PM-VERBATIM-BEGIN PM3:✱250·113
✱250·113.  ⊢ . connex ∩ Bord = Ω
PM-VERBATIM-END PM3:✱250·113 -/

/- PM-VERBATIM-BEGIN PM3:✱250·12
✱250·12.  ⊢ : P ∈ Ω .≡ . P ∈ Ser ∩ Bord  [(*250·02)]
PM-VERBATIM-END PM3:✱250·12 -/

/- PM-VERBATIM-BEGIN PM3:✱250·121
✱250·121.  ⊢ :: P ∈ Ω .≡ : P ∈ Ser : α ⊂ CʻP . ∃! α .⊃ₐ . E! minₚʻα :
  ≡ : P ∈ Ser : ∃! α ∩ CʻP .⊃ₐ . E! minₚʻα  [✱250·12·111]
PM-VERBATIM-END PM3:✱250·121 -/

/- PM-VERBATIM-BEGIN PM3:✱250·122
✱250·122.  ⊢ :: P ∈ Ω .≡ : P ∈ Ser : ∃! CʻP ∩ pʻPʻʻ(α ∩ CʻP) .⊃ₐ . E! seqₚʻα
PM-VERBATIM-END PM3:✱250·122 -/

/- PM-VERBATIM-BEGIN PM3:✱250·123
✱250·123.  ⊢ :: P ∈ Ω − ιʻΛ .≡ : P ∈ Ser : ∃! pʻPʻʻ(α ∩ CʻP) .⊃ₐ . E! seqₚʻα
PM-VERBATIM-END PM3:✱250·123 -/

/- PM-VERBATIM-BEGIN PM3:✱250·124
✱250·124.  ⊢ : P ∈ Ω .≡ . P ∈ Ser . sectʻP − ιʻCʻP ⊂ ∃ʻseqₚ
PM-VERBATIM-END PM3:✱250·124 -/

/- PM-VERBATIM-BEGIN PM3:✱250·125
✱250·125.  ⊢ : P ∈ Ω .≡ . E!! minₚʻʻCl exʻCʻP  [✱250·112·113]
PM-VERBATIM-END PM3:✱250·125 -/

/- PM-VERBATIM-BEGIN PM3:✱250·126
✱250·126.  ⊢ : P ∈ Ω . E! maxₚʻα .∼ E! seqₚʻα .⊃ . BʻP ∈ α . BʻP = maxₚʻα
PM-VERBATIM-END PM3:✱250·126 -/

/- PM-VERBATIM-BEGIN PM3:✱250·13
✱250·13.  ⊢ : P ∈ Ω − ιʻΛ .⊃ . E! BʻP
PM-VERBATIM-END PM3:✱250·13 -/

/- PM-VERBATIM-BEGIN PM3:✱250·131
✱250·131.  ⊢ :: P ∈ Ω .⊃ : ∃! P .≡ . E! BʻP
PM-VERBATIM-END PM3:✱250·131 -/

/- PM-VERBATIM-BEGIN PM3:✱250·14
✱250·14.  ⊢ : P ∈ Bord .⊃ . RlʻP ⊂ Bord
PM-VERBATIM-END PM3:✱250·14 -/

/- PM-VERBATIM-BEGIN PM3:✱250·141
✱250·141.  ⊢ : P ∈ Ω .⊃ . P ▷ α ∈ Ω  [✱250·14 . ✱204·4]
PM-VERBATIM-END PM3:✱250·141 -/

/- PM-VERBATIM-BEGIN PM3:✱250·142
✱250·142.  ⊢ : P ∈ Bord .⊃ . RlʻP ∩ connex ⊂ Ω
PM-VERBATIM-END PM3:✱250·142 -/

/- PM-VERBATIM-BEGIN PM3:✱250·15
✱250·15.  ⊢ : P ∈ Ω . E! BʻP .⊃ . P ∈ Ded
PM-VERBATIM-END PM3:✱250·15 -/

/- PM-VERBATIM-BEGIN PM3:✱250·151
✱250·151.  ⊢ : P ∈ Ω . x ∈ CʻP .⊃ . P ▷ P⁎ʻx ∈ Ded
PM-VERBATIM-END PM3:✱250·151 -/

/- PM-VERBATIM-BEGIN PM3:✱250·152
✱250·152.  ⊢ . Ω ⊂ semi Ded  [✱214·7 . ✱250·124]
PM-VERBATIM-END PM3:✱250·152 -/

/- PM-VERBATIM-BEGIN PM3:✱250·16
✱250·16.  ⊢ : P ∈ Ω . ∃! α ∩ CʻP .⊃ . P⃗ʻminₚʻα = pʻPʻʻ(α ∩ CʻP)
  [✱205·65 . ✱250·121]
PM-VERBATIM-END PM3:✱250·16 -/

/- PM-VERBATIM-BEGIN PM3:✱250·17
✱250·17.  ⊢ :: P, Q ∈ Ω − ιʻΛ .⊃ : P smor Q .≡ . P ▷ ∃ʻP smor Q ▷ ∃ʻQ
  [✱204·47 . ✱250·13]
PM-VERBATIM-END PM3:✱250·17 -/

/- PM-VERBATIM-BEGIN PM3:✱250·2
✱250·2.  ⊢ : P ∈ Bord .⊃ . DʻP = Dʻ(P − P²)
PM-VERBATIM-END PM3:✱250·2 -/

/- PM-VERBATIM-BEGIN PM3:✱250·21
✱250·21.  ⊢ : P ∈ Ω .⊃ . DʻP = DʻP₁  [✱201·63 . ✱250·2]
PM-VERBATIM-END PM3:✱250·21 -/

/- PM-VERBATIM-BEGIN PM3:✱250·22
✱250·22.  ⊢ : P ∈ Ser ∩ Ded . DʻP = DʻP₁ .⊃ . P ∈ Ω − ιʻΛ
PM-VERBATIM-END PM3:✱250·22 -/

/- PM-VERBATIM-BEGIN PM3:✱250·23
✱250·23.  ⊢ : P ∈ Ω . E! BʻP .≡ . P ∈ Ser ∩ Ded . DʻP = DʻP₁
PM-VERBATIM-END PM3:✱250·23 -/

/- PM-VERBATIM-BEGIN PM3:✱250·24
✱250·24.  ⊢ : P ∈ Ω .⊃ . P² | P₁ = P ▷ DʻP
PM-VERBATIM-END PM3:✱250·24 -/

/- PM-VERBATIM-BEGIN PM3:✱250·241
✱250·241.  ⊢ : P ∈ Ω .⊃ . P₁ | P² = (CʻP₁) 1 P  [Proof as in ✱250·24]
PM-VERBATIM-END PM3:✱250·241 -/

/- PM-VERBATIM-BEGIN PM3:✱250·242
✱250·242.  ⊢ : P ∈ Ω .⊃ . P = P₁ ∪ P₁ | P
PM-VERBATIM-END PM3:✱250·242 -/

/- PM-VERBATIM-BEGIN PM3:✱250·243
✱250·243.  ⊢ : P ∈ Ω .⊃ . P ▷ (CʻP₁) = (CʻP₁) 1 (P₁ ∪ P | P₁)
  [Proof as in ✱250·242]
PM-VERBATIM-END PM3:✱250·243 -/

/- PM-VERBATIM-BEGIN PM3:✱250·3
✱250·3.  ⊢ :: P ∈ Bord : α ⊂ CʻP ∩ σ .⊃ₐ . seqₚʻα ⊂ σ : ⊃ₐ . CʻP ⊂ σ
PM-VERBATIM-END PM3:✱250·3 -/

/- PM-VERBATIM-BEGIN PM3:✱250·301
✱250·301.  ⊢ : P ∈ connex . ∼∃! minₚʻτ . σ = CʻP − P⃗ʻτ . α ⊂ σ .⊃ . seqₚʻα ⊂ σ
PM-VERBATIM-END PM3:✱250·301 -/

/- PM-VERBATIM-BEGIN PM3:✱250·31
✱250·31.  ⊢ :: P ∈ connex :: α ⊂ CʻP ∩ σ .⊃ₐ . seqₚʻα ⊂ σ : ⊃ₐ . CʻP ⊂ σ :: ⊃ . P ∈ Ω
PM-VERBATIM-END PM3:✱250·31 -/

/- PM-VERBATIM-BEGIN PM3:✱250·32
✱250·32.  ⊢ :: P ∈ connex .⊃ :: P ∈ Bord .≡ :: α ⊂ CʻP ∩ σ .⊃ₐ . seqₚʻα ⊂ σ :
  ⊃ₐ . CʻP ⊂ σ  [✱250·3·31]
PM-VERBATIM-END PM3:✱250·32 -/

/- PM-VERBATIM-BEGIN PM3:✱250·33
✱250·33.  ⊢ . Ω = connex ∩ P̂ {α ⊂ CʻP ∩ σ .⊃ₐ . seqₚʻα ⊂ σ : ⊃ₐ . CʻP ⊂ σ}
  [✱250·32·113]
PM-VERBATIM-END PM3:✱250·33 -/

/- PM-VERBATIM-BEGIN PM3:✱250·34
✱250·34.  ⊢ :: P ∈ Bord : x ∈ CʻP . P⃗ʻx ⊂ σ .⊃ₓ . x ∈ σ : ⊃ₐ . CʻP ⊂ σ
PM-VERBATIM-END PM3:✱250·34 -/

/- PM-VERBATIM-BEGIN PM3:✱250·341
✱250·341.  ⊢ :: x ∈ CʻP . P⃗ʻx ⊂ σ .⊃ₓ . x ∈ σ : ⊃ₐ . CʻP ⊂ σ :: ⊃ . P ∈ Bord
PM-VERBATIM-END PM3:✱250·341 -/

/- PM-VERBATIM-BEGIN PM3:✱250·35
✱250·35.  ⊢ . Bord = P̂ {x ∈ CʻP . P⃗ʻx ⊂ σ .⊃ₓ . x ∈ σ : ⊃ₐ . CʻP ⊂ σ}
  [✱250·34·341]
PM-VERBATIM-END PM3:✱250·35 -/

/- PM-VERBATIM-BEGIN PM3:✱250·36
✱250·36.  ⊢ :: P ∈ Ω : λ ⊂ σ . ∃! λ ∩ CʻP .⊃ₗ . seqₚʻλ ⊂ σ : ⊃ . P⃗ʻσ ⊂ σ
PM-VERBATIM-END PM3:✱250·36 -/

/- PM-VERBATIM-BEGIN PM3:✱250·361
✱250·361.  ⊢ :: P ∈ Ω . P̈ʻσ ⊂ σ : λ ⊂ σ . ∃! (λ ∩ CʻP) .⊃ₗ . limaxₚʻλ ⊂ σ :
  ⊃ . P̈ʻσ ⊂ σ
PM-VERBATIM-END PM3:✱250·361 -/

/- PM-VERBATIM-BEGIN PM3:✱250·362
✱250·362.  ⊢ :: P ∈ Ω . P₁̈σ ⊂ σ : λ ⊂ σ . ∃! λ ∩ CʻP .⊃ₗ . liminₚʻλ ⊂ σ :
  ⊃ . P̈ʻσ ⊂ σ  [✱250·361 / ✱121·26]
PM-VERBATIM-END PM3:✱250·362 -/

/- PM-VERBATIM-BEGIN PM3:✱250·4
✱250·4.  ⊢ . Λ ∈ Ω
PM-VERBATIM-END PM3:✱250·4 -/

/- PM-VERBATIM-BEGIN PM3:✱250·41
✱250·41.  ⊢ : x ≠ y .⊃ . x ↓ y ∈ Ω
PM-VERBATIM-END PM3:✱250·41 -/

/- PM-VERBATIM-BEGIN PM3:✱250·42
✱250·42.  ⊢ : P ∈ Ω − ιʻΛ .⊃ . E! 2ₚ . 2ₚ = P⃗₁ʻBʻP . P⃗ʻ2ₚ = ιʻBʻP . P ▷ P⃗ʻ2ₚ = Λ
PM-VERBATIM-END PM3:✱250·42 -/

/- PM-VERBATIM-BEGIN PM3:✱250·43
✱250·43.  ⊢ . 0ᵣ = Ω ∩ Cʻʻ0
PM-VERBATIM-END PM3:✱250·43 -/

/- PM-VERBATIM-BEGIN PM3:✱250·44
✱250·44.  ⊢ . 2ᵣ = Ω ∩ Cʻʻ2
PM-VERBATIM-END PM3:✱250·44 -/

/- PM-VERBATIM-BEGIN PM3:✱250·5
✱250·5.  ⊢ : P ∈ Ω .⊃ . minₚ ▷ Cl exʻCʻP ∈ εₐʻCl exʻCʻP . ιʻCʻP = ProdʻCl exʻCʻP
  [✱205·33 . ✱250·1 . ✱115·17]
PM-VERBATIM-END PM3:✱250·5 -/

/- PM-VERBATIM-BEGIN PM3:✱250·51
✱250·51.  ⊢ : α ∈ CʻʻΩ .⊃ . ∃! εₐʻCl exʻα  [✱250·5]
PM-VERBATIM-END PM3:✱250·51 -/

/- PM-VERBATIM-BEGIN PM3:✱250·52
✱250·52.  ⊢ : α ∈ CʻʻΩ . β ⊂ α .⊃ . ∃! εₐʻCl exʻβ  [✱88·22·2 . ✱250·51]
PM-VERBATIM-END PM3:✱250·52 -/

/- PM-VERBATIM-BEGIN PM3:✱250·53
✱250·53.  ⊢ : sʻκ ∈ CʻʻΩ . Λ ∼ ε κ .⊃ . ∃! εₐʻκ
PM-VERBATIM-END PM3:✱250·53 -/

/- PM-VERBATIM-BEGIN PM3:✱250·54
✱250·54.  ⊢ : CʻʻΩ ∪ 1 = Cls .⊃ . Mult ax
PM-VERBATIM-END PM3:✱250·54 -/

/- PM-VERBATIM-BEGIN PM3:✱250·6
✱250·6.  ⊢ : P, Q ∈ Ω . P smor Q .⊃ . P smor Q ∈ 1  [✱208·41 . ✱250·12·1]
PM-VERBATIM-END PM3:✱250·6 -/

/- PM-VERBATIM-BEGIN PM3:✱250·61
✱250·61.  ⊢ : P ∈ Ω .⊃ . P smor P = ιʻ(I | CʻP)  [✱208·42]
PM-VERBATIM-END PM3:✱250·61 -/

/- PM-VERBATIM-BEGIN PM3:✱250·62
✱250·62.  ⊢ : P ∈ Bord . S ∈ crorʻP .⊃ . ∼(∃x) . (Sʻx) P x  [✱208·43]
PM-VERBATIM-END PM3:✱250·62 -/

/- PM-VERBATIM-BEGIN PM3:✱250·63
✱250·63.  ⊢ : P ∈ Ω ∩ CnvʻʻΩ .⊃ . RlʻP ∩ NrʻP = ιʻP  [✱208·45]
PM-VERBATIM-END PM3:✱250·63 -/

/- PM-VERBATIM-BEGIN PM3:✱250·64
✱250·64.  ⊢ : P ∈ Bord . S ∈ crorʻP .⊃ . CʻP ∩ pʻP⃗ʻDʻS = Λ  [✱208·46]
PM-VERBATIM-END PM3:✱250·64 -/

/- PM-VERBATIM-BEGIN PM3:✱250·65
✱250·65.  ⊢ : P ∈ Ω . α ∈ sectʻP − ιʻCʻP . β ⊂ α .⊃ . ∼(P smor P ▷ β)
PM-VERBATIM-END PM3:✱250·65 -/

/- PM-VERBATIM-BEGIN PM3:✱250·651
✱250·651.  ⊢ : P ∈ Ω .⊃ . NrʻP ∩ P ▷ ʻʻ(sectʻP − ιʻCʻP) = Λ  [✱250·65]
PM-VERBATIM-END PM3:✱250·651 -/

/- PM-VERBATIM-BEGIN PM3:✱250·652
✱250·652.  ⊢ : P ∈ Bord . Q ⊂ P . ∃! CʻP ∩ pʻP⃗ʻʻCʻQ .⊃ . ∼(P smor Q)
  [✱208·47]
PM-VERBATIM-END PM3:✱250·652 -/

/- PM-VERBATIM-BEGIN PM3:✱250·653
✱250·653.  ⊢ : P ∈ Bord . ∃! CʻP ∩ pʻP⃗ʻʻ(α ∩ CʻP) .⊃ . ∼(P smor P ▷ α)
PM-VERBATIM-END PM3:✱250·653 -/

/- PM-VERBATIM-BEGIN PM3:✱250·66
✱250·66.  ⊢ : P ∈ Ω . α ∈ sectʻP . P smor (P ▷ α) .⊃ . α = CʻP  [✱250·65 . Transp]
PM-VERBATIM-END PM3:✱250·66 -/

/- PM-VERBATIM-BEGIN PM3:✱250·67
✱250·67.  ⊢ : P ∈ Ω . x ∈ CʻP .⊃ . ∼(P smor (P ▷ P⃗ʻx))
PM-VERBATIM-END PM3:✱250·67 -/

/- PM-VERBATIM-BEGIN PM3:✱250·7
✱250·7.  ⊢ :: P ∈ Ω .≡ : x ∈ CʻP .⊃ₓ . P ▷ P⁎ʻx ∈ Ω : P ∈ Ser
PM-VERBATIM-END PM3:✱250·7 -/
