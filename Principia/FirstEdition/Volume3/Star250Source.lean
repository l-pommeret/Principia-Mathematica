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
