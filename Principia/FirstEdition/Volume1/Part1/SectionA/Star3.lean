import Principia.Deduction.Formed
import Principia.FirstEdition.Volume1.Part1.SectionA.Star2

namespace PM.Elementary

/-- ✱3·01. Logical product is a definitional abbreviation, not a primitive
connective and not Lean's native conjunction. -/
def conj (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  ∼ₚ (∼ₚ p ∨ₚ ∼ₚ q)

infixl:56 " ∧ₚ " => conj

/-- ✱3·02. The printed chain is the product of its two adjacent implications;
it is not parsed as a right-associated implication chain. -/
def impChain (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  conj (p ⊃ₚ q) (q ⊃ₚ r)

end PM.Elementary

namespace PM.FirstEdition.Volume1.Star3

open PM
open PM.Elementary

/- PM-VERBATIM-BEGIN PM1:✱3·01
✱3·01.  p . q .=. ∼(∼p ∨ ∼q)     Df
PM-VERBATIM-END PM1:✱3·01 -/

/- PM-VERBATIM-BEGIN PM1:✱3·02
✱3·02.  p ⊃ q ⊃ r .=. p ⊃ q . q ⊃ r     Df
PM-VERBATIM-END PM1:✱3·02 -/

/- PM-FORMAL-GLOSS
The dot between p and q in ✱3·01 is the newly defined logical product. In
✱3·02 the two dots on the right delimit the product of the adjacent
implications. Neither definition is an asserted equivalence proposition.
-/

def star_3_01_printed : PM.PrintedFormula :=
  PM.pmPrinted "p . q .=. ∼(∼p ∨ ∼q)     Df"

def star_3_02_printed : PM.PrintedFormula :=
  PM.pmPrinted "p ⊃ q ⊃ r .=. p ⊃ q . q ⊃ r     Df"

/- PM-VERBATIM-BEGIN PM1:✱3·03
✱3·03. Given two asserted elementary propositional functions “⊢ . φp” and
“⊢ . ψp” whose arguments are elementary propositions, we have ⊢ . φp . ψp.

Dem.

⊢ . ✱1·7·72 . ✱2·11 . ⊃ ⊢ : ∼φp ∨ ∼ψp . ∨ . ∼(∼φp ∨ ∼ψp)              (1)
⊢ . (1) . ✱2·32 . (✱1·01) . ⊃ ⊢ : φp . ⊃ : ψp . ⊃ . ∼(∼φp ∨ ∼ψp)      (2)
⊢ . (2) . (✱3·03) . ⊃ ⊢ : φp . ⊃ : ψp . ⊃ . φp . ψp                   (3)
⊢ . (3) . ✱1·11 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·03 -/

/- PM-EDITORIAL
The canonical first-edition scan prints `(✱3·03)` in the third line of the
demonstration, a circular self-reference. The formula and the preceding
explanation require the definition ✱3·01; the likely correction is therefore
`(✱3·01)`, but the diplomatic bytes above retain the print. This locus remains
classified as an uncertain apparent print error pending a second physical
witness. Project Gutenberg repeats the circular reference and independently
corrupts some φ/ψ glyphs, so it cannot establish an authorial correction.

Sources: printed pp. 114 and 116, scan leaves 136 and 138:
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/136
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/138
-/

/-- ✱3·03. Formation-aware product of two asserted elementary propositional
functions with the same nonempty real-variable context.

The returned object makes the printed formation Pp ✱1·7/✱1·72 operational;
its derivation component follows the displayed ✱2·11, ✱2·32, ✱1·01 and
✱1·11 route. -/
theorem star_3_03 {Γ : PM.RealContext} (hasRealVariable : Γ ≠ [])
    {φ ψ : PM.Elementary Γ}
    (hφ : PM.FormedDerivation φ) (hψ : PM.FormedDerivation ψ) :
    PM.FormedDerivation (PM.Elementary.conj φ ψ) := by
  refine ⟨?_, ?_⟩
  · exact PM.Formation.star_1_7
      (PM.Formation.star_1_72 hasRealVariable
        (PM.Formation.star_1_7 hφ.formation)
        (PM.Formation.star_1_7 hψ.formation))
  · have h1 : ⊢ₚ ((∼ₚ φ ∨ₚ ∼ₚ ψ) ∨ₚ ∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)) :=
      PM.FirstEdition.Volume1.Star2.star_2_11 (∼ₚ φ ∨ₚ ∼ₚ ψ)
    have h2 : ⊢ₚ (φ ⊃ₚ (ψ ⊃ₚ PM.Elementary.conj φ ψ)) :=
      PM.Derivation.star_1_11 hasRealVariable h1
        (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ φ) (∼ₚ ψ)
          (∼ₚ (∼ₚ φ ∨ₚ ∼ₚ ψ)))
    exact PM.Derivation.star_1_11 hasRealVariable hψ.derivation
      (PM.Derivation.star_1_11 hasRealVariable hφ.derivation h2)

/- PM-VERBATIM-BEGIN PM1:✱3·1
✱3·1.  ⊢ : p . q . ⊃ . ∼(∼p ∨ ∼q)     [Id . (✱3·01)]
PM-VERBATIM-END PM1:✱3·1 -/

/- PM-VERBATIM-BEGIN PM1:✱3·11
✱3·11.  ⊢ : ∼(∼p ∨ ∼q) . ⊃ . p . q     [Id . (✱3·01)]
PM-VERBATIM-END PM1:✱3·11 -/

/- PM-VERBATIM-BEGIN PM1:✱3·12
✱3·12.  ⊢ : ∼p . ∨ . ∼q . ∨ . p . q     [✱2·11 (∼p ∨ ∼q)/p]
PM-VERBATIM-END PM1:✱3·12 -/

/- PM-VERBATIM-BEGIN PM1:✱3·13
✱3·13.  ⊢ : ∼(p . q) . ⊃ . ∼p ∨ ∼q     [✱3·11 . Transp]
PM-VERBATIM-END PM1:✱3·13 -/

/- PM-VERBATIM-BEGIN PM1:✱3·14
✱3·14.  ⊢ : ∼p ∨ ∼q . ⊃ . ∼(p . q)     [✱3·1 . Transp]
PM-VERBATIM-END PM1:✱3·14 -/

/-- ✱3·1. Id applied to the product, with ✱3·01 made explicit by unfolding
its definitional abbreviation. -/
theorem star_3_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := by
  simpa only [PM.Elementary.conj] using
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)

/-- ✱3·11. The converse reading of the same definitional product. -/
theorem star_3_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ (p ∧ₚ q)) := by
  simpa only [PM.Elementary.conj] using
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)

/-- ✱3·12. ✱2·11 under the printed substitution `(∼p ∨ ∼q)/p`; the two
successive Group-I sum marks are left-associated. -/
theorem star_3_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q)) :=
  PM.FirstEdition.Volume1.Star2.star_2_11 ((∼ₚ p) ∨ₚ (∼ₚ q))

/-- ✱3·13. The printed ✱3·11 followed by the `Transp` form ✱2·15. -/
theorem star_3_13 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) :=
  PM.Derivation.detach (star_3_11 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_15 ((∼ₚ p) ∨ₚ (∼ₚ q)) (p ∧ₚ q))

/-- ✱3·14. The printed ✱3·1 followed by `Transp` (✱2·16), with the
double-negation and syllogism steps that the historical alias suppresses. -/
theorem star_3_14 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (p ∧ₚ q))) := by
  have hImp : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := star_3_1 p q
  have hTransp :
      ⊢ₚ ((∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) ⊃ₚ (∼ₚ (p ∧ₚ q))) :=
    PM.Derivation.detach hImp
      (PM.FirstEdition.Volume1.Star2.star_2_16 (p ∧ₚ q)
        (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))
  have hDN : ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))) :=
    PM.FirstEdition.Volume1.Star2.star_2_12 ((∼ₚ p) ∨ₚ (∼ₚ q))
  exact PM.Derivation.detach hTransp
    (PM.Derivation.detach hDN
      (PM.FirstEdition.Volume1.Star2.star_2_06 ((∼ₚ p) ∨ₚ (∼ₚ q))
        (∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) (∼ₚ (p ∧ₚ q))))

/- PM-VERBATIM-BEGIN PM1:✱3·2
✱3·2.  ⊢ : p . ⊃ : q . ⊃ . p . q   [✱3·12]
PM-VERBATIM-END PM1:✱3·2 -/

/- PM-VERBATIM-BEGIN PM1:✱3·21
✱3·21.  ⊢ : q . ⊃ : p . ⊃ . p . q   [✱3·2 . Comm]
PM-VERBATIM-END PM1:✱3·21 -/

/- PM-VERBATIM-BEGIN PM1:✱3·22
✱3·22.  ⊢ : p . q . ⊃ . q . p

This is one form of the commutative law for logical multiplication. A more
complete form is given in ✱4·3.

Dem.

[✱3·13 (q,p)/(p,q)] ⊢ : ∼(q . p) . ⊃ . ∼q ∨ ∼p :
[Perm] ⊃ : ∼p ∨ ∼q :
[✱3·14] ⊃ : ∼(p . q)   (1)
⊢ . (1) . Transp . ⊃ ⊢ . Prop

Note. In the above proof, (1) stands for ∼(q . p) . ⊃ . ∼(p . q).
PM-VERBATIM-END PM1:✱3·22 -/

/- PM-VERBATIM-BEGIN PM1:✱3·24
✱3·24.  ⊢ . ∼(p . ∼p)

Dem.

[✱2·11 ∼p/p] ⊢ . ∼p ∨ ∼(∼p) . ⊃
[✱3·14 ∼p/q] ⊢ . ∼(p . ∼p)

The above is the law of contradiction.
PM-VERBATIM-END PM1:✱3·24 -/

/-- ✱3·2. The printed citation omits the required ✱2·32 reassociation. -/
theorem star_3_2 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ q))) :=
  PM.Derivation.detach (star_3_12 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ p) (∼ₚ q) (p ∧ₚ q))

theorem star_3_21 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ⊃ₚ (p ∧ₚ q))) :=
  PM.Derivation.detach (star_3_2 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_04 p q (p ∧ₚ q))

theorem star_3_22 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ p)) :=
  PM.Derivation.detach
    (PM.Derivation.detach (star_3_14 p q)
      (PM.Derivation.detach
        (PM.Derivation.detach
          (PM.FirstEdition.Volume1.Star1.star_1_4 (∼ₚ q) (∼ₚ p))
          (PM.Derivation.detach (star_3_13 q p)
            (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
              ((∼ₚ q) ∨ₚ (∼ₚ p)) ((∼ₚ p) ∨ₚ (∼ₚ q)))))
        (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
          ((∼ₚ p) ∨ₚ (∼ₚ q)) (∼ₚ (p ∧ₚ q)))))
    (PM.FirstEdition.Volume1.Star2.star_2_17 (p ∧ₚ q) (q ∧ₚ p))

theorem star_3_24 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (p ∧ₚ (∼ₚ p))) :=
  PM.Derivation.detach
    (PM.FirstEdition.Volume1.Star2.star_2_11 (∼ₚ p))
    (star_3_14 p (∼ₚ p))

/- PM-VERBATIM-BEGIN PM1:✱3·37
✱3·37.  ⊢ : p . q . ⊃ . r : ⊃ : p . ∼r . ⊃ . ∼q

Dem.

⊢ . Transp . ⊃ ⊢ : q ⊃ r . ⊃ . ∼r ⊃ ∼q :
[Syll] ⊃ ⊢ : p . ⊃ . q ⊃ r : ⊃ : p . ⊃ . ∼r ⊃ ∼q   (1)
⊢ . Exp . ⊃ ⊢ : p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r   (2)
⊢ . Imp . ⊃ ⊢ : p . ⊃ . ∼r ⊃ ∼q : ⊃ : p . ∼r . ⊃ . ∼q   (3)
⊢ . (2) . (1) . (3) . Syll . ⊃ ⊢ . Prop

This is another form of transposition.
PM-VERBATIM-END PM1:✱3·37 -/

/- PM-VERBATIM-BEGIN PM1:✱3·4
✱3·4.  ⊢ : p . q . ⊃ . p ⊃ q   [✱2·51 . Transp . (✱1·01 . ✱3·01)]
PM-VERBATIM-END PM1:✱3·4 -/

/- PM-VERBATIM-BEGIN PM1:✱3·41
✱3·41.  ⊢ : p ⊃ r . ⊃ : p . q . ⊃ . r   [✱3·26 . Syll]
PM-VERBATIM-END PM1:✱3·41 -/

/- PM-VERBATIM-BEGIN PM1:✱3·42
✱3·42.  ⊢ : q ⊃ r . ⊃ : p . q . ⊃ . r   [✱3·27 . Syll]
PM-VERBATIM-END PM1:✱3·42 -/

/- PM-VERBATIM-BEGIN PM1:✱3·43
✱3·43.  ⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q . r

Dem.

⊢ . ✱3·2 . ⊃ ⊢ : q . ⊃ : r . ⊃ . q . r   (1)
⊢ . (1) . Syll . ⊃ ⊢ :: p ⊃ q . ⊃ : p . ⊃ : r . ⊃ . q . r :
[✱2·77] ⊃ : p ⊃ r . ⊃ : p . ⊃ . q . r   (2)
⊢ . (2) . Imp . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·43 -/

/- PM-VERBATIM-BEGIN PM1:✱3·44
✱3·44.  ⊢ : q ⊃ p . r ⊃ p . ⊃ : q ∨ r . ⊃ . p

This principle is analogous to ✱3·43. The analogy between ✱3·43 and ✱3·44
is of a sort which generally subsists between formulae concerning products and
formulae concerning sums.

Dem.

⊢ . Syll . ⊃ ⊢ : ∼q ⊃ r . r ⊃ p . ⊃ : ∼q ⊃ p :
[✱2·6] ⊃ : q ⊃ p . ⊃ . p   (1)
⊢ . (1) . Exp . ⊃ ⊢ :: ∼q ⊃ r . ⊃ : r ⊃ p . ⊃ : q ⊃ p . ⊃ . p :
[Comm . Imp] ⊃ : q ⊃ p . r ⊃ p . ⊃ . p   (2)
⊢ . (2) . Comm . ⊃ ⊢ : q ⊃ p . r ⊃ p . ⊃ : ∼q ⊃ r . ⊃ . p :
[✱2·53 . Syll] ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·44 -/

/- PM-VERBATIM-BEGIN PM1:✱3·45
✱3·45.  ⊢ : p ⊃ q . ⊃ : p . r . ⊃ . q . r

This principle shows that we may multiply both sides of an implication by a
common factor; hence it is called by Peano the "principle of the factor." We
shall refer to it as "Fact." It is the analogue, for multiplication, of the
primitive proposition ✱1·6.

Dem.

⊢ . Syll ∼r/r . ⊃ ⊢ : p ⊃ q . ⊃ : q ⊃ ∼r . ⊃ . p ⊃ ∼r :
[Transp] ⊃ : ∼(p ⊃ ∼r) . ⊃ . ∼(q ⊃ ∼r) :
[Id . (✱1·01 . ✱3·01)] ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·45 -/

/- PM-VERBATIM-BEGIN PM1:✱3·47
✱3·47.  ⊢ : p ⊃ r . q ⊃ s . ⊃ : p . q . ⊃ . r . s

This proposition, or rather its analogue for classes, was proved by Leibniz,
and evidently pleased him, since he calls it "præclarum theorema*."

Dem.

⊢ . ✱3·26 . ⊃ ⊢ : p ⊃ r . q ⊃ s . ⊃ : p ⊃ r :
[Fact] ⊃ : p . q . ⊃ . r . q:
[✱3·22] ⊃ : p . q . ⊃ . q . r   (1)
⊢ . ✱3·27 . ⊃ ⊢ : p ⊃ r . q ⊃ s . ⊃ : q ⊃ s:
[Fact] ⊃ : q . r . ⊃ . s . r:
[✱3·22] ⊃ : q . r . ⊃ . r . s   (2)
⊢ . (1) . (2) . ✱3·03 . ✱2·83 . ⊃ ⊢ . Prop

* Philosophical works, Gerhardt's edition, Vol. vii. p. 223.
PM-VERBATIM-END PM1:✱3·47 -/

/- PM-VERBATIM-BEGIN PM1:✱3·48
✱3·48.  ⊢ : p ⊃ r . q ⊃ s . ⊃ : p ∨ q . ⊃ . r ∨ s

This theorem is the analogue of ✱3·47.

Dem.

⊢ . ✱3·26 . ⊃ ⊢ : p ⊃ r . q ⊃ s . ⊃ : p ⊃ r:
[Sum] ⊃ : p ∨ q . ⊃ . r ∨ q:
[Perm] ⊃ : p ∨ q . ⊃ . q ∨ r   (1)
⊢ . ✱3·27 . ⊃ ⊢ : p ⊃ r . q ⊃ s . ⊃ : q ⊃ s:
[Sum] ⊃ : q ∨ r . ⊃ . s ∨ r:
[Perm] ⊃ : q ∨ r . ⊃ . r ∨ s   (2)
⊢ . (1) . (2) . ✱2·83 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·48 -/

end PM.FirstEdition.Volume1.Star3
