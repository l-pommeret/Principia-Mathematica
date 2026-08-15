import Principia.Deduction.Formed
import Principia.Deduction.PrintedNames
import Principia.FirstEdition.Volume1.Part1.SectionA.Star1
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

/-- ✱1·01, used as the explicit definitional rewrite printed in ✱3. -/
theorem star_1_01 {Γ} (p q : PM.Elementary Γ) :
    (p ⊃ₚ q) = ((∼ₚ p) ∨ₚ q) := rfl

/-- ✱3·01, used as the explicit definitional rewrite printed in ✱3. -/
theorem star_3_01 {Γ} (p q : PM.Elementary Γ) :
    (p ∧ₚ q) = ∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)) := rfl

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

/- ✱3·1. Id applied to the product, with ✱3·01 made explicit by unfolding
its definitional abbreviation. -/
/-- Audited scope reading of ✱3·1. -/
def star_3_1_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . ∼(∼p ∨ ∼q)     [Id . (✱3·01)]"
  parsed := (p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))
  scopeReading := "The product p . q is the antecedent; ∼(∼p ∨ ∼q) is the consequent."

theorem star_3_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := by
  have line1 : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ q)) :=
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)
  rw [star_3_01 p q] at line1
  exact line1

/- ✱3·11. The converse reading of the same definitional product. -/
/-- Audited scope reading of ✱3·11. -/
def star_3_11_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼(∼p ∨ ∼q) . ⊃ . p . q     [Id . (✱3·01)]"
  parsed := (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ (p ∧ₚ q)
  scopeReading := "∼(∼p ∨ ∼q) is the antecedent; the product p . q is the consequent."

theorem star_3_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ (p ∧ₚ q)) := by
  have line1 : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ q)) :=
    PM.FirstEdition.Volume1.Star2.star_2_08 (p ∧ₚ q)
  rw [star_3_01 p q] at line1
  exact line1

/- ✱3·12. ✱2·11 under the printed substitution `(∼p ∨ ∼q)/p`; the two
successive Group-I sum marks are left-associated. -/
/-- Audited scope reading of ✱3·12. -/
def star_3_12_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼p . ∨ . ∼q . ∨ . p . q     [✱2·11 (∼p ∨ ∼q)/p]"
  parsed := ((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q)
  scopeReading := "The successive disjunctions are left-associated, with p . q as the final disjunct."

theorem star_3_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ (p ∧ₚ q)) :=
  PM.FirstEdition.Volume1.Star2.star_2_11 ((∼ₚ p) ∨ₚ (∼ₚ q))

/- ✱3·13. The printed ✱3·11 followed by the `Transp` form ✱2·15. -/
/-- Audited scope reading of ✱3·13. -/
def star_3_13_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼(p . q) . ⊃ . ∼p ∨ ∼q     [✱3·11 . Transp]"
  parsed := (∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))
  scopeReading := "The negation of the product is the antecedent; ∼p ∨ ∼q is the consequent."

theorem star_3_13 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) :=
  PM.Derivation.detach (star_3_11 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_15 ((∼ₚ p) ∨ₚ (∼ₚ q)) (p ∧ₚ q))

/- ✱3·14. The printed ✱3·1 followed by `Transp` (✱2·16), with the
double-negation and syllogism steps that the historical alias suppresses. -/
/-- Audited scope reading of ✱3·14. -/
def star_3_14_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼p ∨ ∼q . ⊃ . ∼(p . q)     [✱3·1 . Transp]"
  parsed := ((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ (∼ₚ (p ∧ₚ q))
  scopeReading := "∼p ∨ ∼q is the antecedent; the negation of the product is the consequent."

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
✱3·2.  ⊢ :. p . ⊃ : q . ⊃ . p . q   [✱3·12]
PM-VERBATIM-END PM1:✱3·2 -/

/- PM-VERBATIM-BEGIN PM1:✱3·21
✱3·21.  ⊢ :. q . ⊃ : p . ⊃ . p . q   [✱3·2 . Comm]
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

/- ✱3·2. The printed citation omits the required ✱2·32 reassociation. -/
/-- Audited scope reading of ✱3·2. -/
def star_3_2_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. p . ⊃ : q . ⊃ . p . q"
  parsed := p ⊃ₚ (q ⊃ₚ (p ∧ₚ q))
  scopeReading := "The nested dots make p the outer antecedent and q the inner antecedent of the product conclusion."

theorem star_3_2 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (q ⊃ₚ (p ∧ₚ q))) :=
  PM.Derivation.detach (star_3_12 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ p) (∼ₚ q) (p ∧ₚ q))

/-- Audited scope reading of ✱3·21. -/
def star_3_21_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q . ⊃ : p . ⊃ . p . q"
  parsed := q ⊃ₚ (p ⊃ₚ (p ∧ₚ q))
  scopeReading := "The nested dots make q the outer antecedent and p the inner antecedent of the product conclusion."

theorem star_3_21 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ⊃ₚ (p ∧ₚ q))) :=
  PM.Derivation.detach (star_3_2 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_04 p q (p ∧ₚ q))

/-- Audited scope reading of ✱3·22. -/
def star_3_22_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . q . p"
  parsed := (p ∧ₚ q) ⊃ₚ (q ∧ₚ p)
  scopeReading := "The product p . q is the antecedent and the reversed product q . p is the consequent."

theorem star_3_22 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ p)) :=
  PM.Derivation.detach
    (PM.Derivation.detach (star_3_14 p q)
      (PM.Derivation.detach
        (PM.Derivation.detach
          (PM.Derivation.star_1_4 (∼ₚ q) (∼ₚ p))
          (PM.Derivation.detach (star_3_13 q p)
            (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
              ((∼ₚ q) ∨ₚ (∼ₚ p)) ((∼ₚ p) ∨ₚ (∼ₚ q)))))
        (PM.FirstEdition.Volume1.Star2.star_2_06 (∼ₚ (q ∧ₚ p))
          ((∼ₚ p) ∨ₚ (∼ₚ q)) (∼ₚ (p ∧ₚ q)))))
    (PM.FirstEdition.Volume1.Star2.star_2_17 (p ∧ₚ q) (q ∧ₚ p))

/-- Audited scope reading of ✱3·24. -/
def star_3_24_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . ∼(p . ∼p)"
  parsed := ∼ₚ (p ∧ₚ (∼ₚ p))
  scopeReading := "The outer negation applies to the whole product p . ∼p."

theorem star_3_24 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (p ∧ₚ (∼ₚ p))) :=
  PM.Derivation.detach
    (PM.FirstEdition.Volume1.Star2.star_2_11 (∼ₚ p))
    (star_3_14 p (∼ₚ p))

/- PM I (1910), p. 117, ✱3·26. -/
/-- Audited scope reading of ✱3·26. -/
def star_3_26_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . p"
  parsed := (p ∧ₚ q) ⊃ₚ p
  scopeReading := "The product p . q is the antecedent; p is the consequent."

theorem star_3_26 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ p) := by
  have line1 : ⊢ₚ (p ⊃ₚ (q ⊃ₚ p)) :=
    PM.FirstEdition.Volume1.Star2.star_2_02 q p
  rw [star_1_01 p (q ⊃ₚ p), star_1_01 q p] at line1
  have line2 : ⊢ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ p) :=
    PM.Derivation.detach
      (PM.Derivation.detach line1
        (PM.FirstEdition.Volume1.Star2.star_2_31 (∼ₚ p) (∼ₚ q) p))
      (PM.FirstEdition.Volume1.Star2.star_2_53 ((∼ₚ p) ∨ₚ (∼ₚ q)) p)
  rw [← star_3_01 p q] at line2
  exact line2

/- PM I (1910), p. 117, ✱3·27. The printed chain leaves its one
composition step implicit; see the documented ✱1·6 relaxation. -/
/-- Audited scope reading of ✱3·27. -/
def star_3_27_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . q"
  parsed := (p ∧ₚ q) ⊃ₚ q
  scopeReading := "The product p . q is the antecedent; q is the consequent."

theorem star_3_27 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ q) :=
  PM.Derivation.detach (star_3_22 p q)
    (PM.Derivation.detach (star_3_26 q p)
      (PM.Derivation.star_1_6 (∼ₚ (p ∧ₚ q)) (q ∧ₚ p) q))

/-- Audited scope reading of ✱3·3. -/
def star_3_3_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r"
  parsed := ((p ∧ₚ q) ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r))
  scopeReading := "The major dots group (p . q) ⊃ r as antecedent and p ⊃ (q ⊃ r) as consequent."

theorem star_3_3 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r))) := by
  have line1 := PM.FirstEdition.Volume1.Star2.star_2_15 ((∼ₚ p) ∨ₚ (∼ₚ q)) r
  have line2 := PM.FirstEdition.Volume1.Star2.star_2_04 (∼ₚ r) p (∼ₚ q)
  have line3 := PM.Derivation.detach
    (PM.FirstEdition.Volume1.Star2.star_2_17 q r)
    (PM.FirstEdition.Volume1.Star2.star_2_05 p ((∼ₚ r) ⊃ₚ (∼ₚ q)) (q ⊃ₚ r))
  have line4 := PM.Derivation.detach line2
    (PM.Derivation.detach line1 (PM.FirstEdition.Volume1.Star2.star_2_06
      ((p ∧ₚ q) ⊃ₚ r) ((∼ₚ r) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))
      (p ⊃ₚ ((∼ₚ r) ⊃ₚ (∼ₚ q)))))
  have line5 := PM.Derivation.detach line3 (PM.Derivation.detach line4
    (PM.FirstEdition.Volume1.Star2.star_2_06 ((p ∧ₚ q) ⊃ₚ r)
      (p ⊃ₚ ((∼ₚ r) ⊃ₚ (∼ₚ q))) (p ⊃ₚ (q ⊃ₚ r))))
  rw [star_3_01 p q, star_1_01 (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) r] at line5
  let T : PM.Elementary Γ := ((p ∧ₚ q) ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r))
  let U : PM.Elementary Γ :=
    ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ r) ⊃ₚ
      ((∼ₚ r) ⊃ₚ (∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))))
  have transp : ⊢ₚ U := PM.FirstEdition.Volume1.Star2.star_2_16
    (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) r
  have identity : ⊢ₚ (T ⊃ₚ T) := PM.FirstEdition.Volume1.Star2.star_2_08 T
  have line5' : ⊢ₚ T := PM.Derivation.detach line5 identity
  exact PM.Derivation.detach transp
    (PM.Derivation.detach line5'
      (PM.FirstEdition.Volume1.Star2.star_2_02 U T))

/- PM I (1910), p. 117, ✱3·31. The printed chain leaves its one
composition step implicit; see the documented ✱1·6 relaxation. -/
/-- Audited scope reading of ✱3·31. -/
def star_3_31_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ⊃ . q ⊃ r : ⊃ : p . q . ⊃ . r"
  parsed := (p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)
  scopeReading := "The major dots group p ⊃ (q ⊃ r) as antecedent and (p . q) ⊃ r as consequent."

theorem star_3_31 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) := by
  have line1 : ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((∼ₚ p) ∨ₚ ((∼ₚ q) ∨ₚ r))) := by
    rw [star_1_01 p (q ⊃ₚ r), star_1_01 q r]
    exact PM.FirstEdition.Volume1.Star2.star_2_08 ((∼ₚ p) ∨ₚ ((∼ₚ q) ∨ₚ r))
  have line2 : ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ r)) :=
    PM.Derivation.detach line1 (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star2.star_2_31 (∼ₚ p) (∼ₚ q) r)
      (PM.FirstEdition.Volume1.Star2.star_2_05
        (p ⊃ₚ (q ⊃ₚ r)) ((∼ₚ p) ∨ₚ ((∼ₚ q) ∨ₚ r))
        (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ r)))
  have line3 : ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ r)) :=
    PM.Derivation.detach line2 (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star2.star_2_53 ((∼ₚ p) ∨ₚ (∼ₚ q)) r)
      (PM.FirstEdition.Volume1.Star2.star_2_05
        (p ⊃ₚ (q ⊃ₚ r)) (((∼ₚ p) ∨ₚ (∼ₚ q)) ∨ₚ r)
        ((∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ r)))
  rw [← star_3_01 p q] at line3
  exact line3

/- PM-VERBATIM-BEGIN PM1:✱3·26
✱3·26.  ⊢ : p . q . ⊃ . p

Dem.

[✱2·02 (q,p)/(p,q)] ⊢ : p . ⊃ . q ⊃ p   (1)
⊢ . (1) . (✱1·01) . ⊃ ⊢ : ∼p . ∨ . ∼q ∨ p :
[✱2·31] ⊃ ⊢ : ∼p ∨ ∼q . ∨ . p :
[✱2·53 (∼p ∨ ∼q,p)/(p,q)] ⊃ ⊢ : ∼(∼p ∨ ∼q) . ⊃ . p   (2)
⊢ . (2) . (✱3·01) . ⊃ ⊢ : p . q . ⊃ . p
PM-VERBATIM-END PM1:✱3·26 -/

/- PM-VERBATIM-BEGIN PM1:✱3·27
✱3·27.  ⊢ : p . q . ⊃ . q

Dem.

[✱3·22] ⊢ : p . q . ⊃ . q . p :
[✱3·26 (q,p)/(p,q)] ⊃ : q . ⊃ ⊢ . Prop

✱3·26·27 will both be called the "principle of simplification," like ✱2·02,
from which they are deduced. They will be referred to as "Simp."
PM-VERBATIM-END PM1:✱3·27 -/

/- PM-VERBATIM-BEGIN PM1:✱3·3
✱3·3.  ⊢ : p . q . ⊃ . r : ⊃ : p . ⊃ . q ⊃ r

Dem.

[Id . (✱3·01)] ⊢ : .p . q . ⊃ . r : ⊃ : ∼(∼p ∨ ∼q) . ⊃ . r :
[Transp] ⊃ : ∼r . ⊃ . ∼p ∨ ∼q :
[Id . (✱1·01)] ⊃ : ∼r . ⊃ . p ⊃ ∼q :
[Comm] ⊃ : p . ⊃ . ∼r ⊃ ∼q :
[Transp . Syll] ⊃ : p . ⊃ . q ⊃ r : . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·3 -/

/- PM-VERBATIM-BEGIN PM1:✱3·31
✱3·31.  ⊢ : p . ⊃ . q ⊃ r : ⊃ : p . q . ⊃ . r

Dem.

[Id . (✱1·01)] ⊢ : .p . ⊃ . q ⊃ r : ⊃ : ∼p . ∨ . ∼q ∨ r :
[✱2·31] ⊃ : ∼p ∨ ∼q . ∨ . r :
[✱2·53 (∼p ∨ ∼q,r)/(p,q)] ⊃ : ∼(∼p ∨ ∼q) . ⊃ . r :
[Id . (✱3·01)] ⊃ : p . q . ⊃ . r : . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·31 -/

/- PM-VERBATIM-BEGIN PM1:✱3·33
✱3·33.  ⊢ : p ⊃ q . q ⊃ r . ⊃ . p ⊃ r     [Syll.Imp]
PM-VERBATIM-END PM1:✱3·33 -/

/- PM-VERBATIM-BEGIN PM1:✱3·34
✱3·34.  ⊢ : q ⊃ r . p ⊃ q . ⊃ . p ⊃ r     [Syll.Imp]
PM-VERBATIM-END PM1:✱3·34 -/

/- PM-VERBATIM-BEGIN PM1:✱3·35
These two propositions will hereafter be referred to as "Syll"; they are
usually more convenient than either ✱2·05 or ✱2·06.

✱3·35.  ⊢ : p . p ⊃ q . ⊃ . q     [✱2·27.Imp]
PM-VERBATIM-END PM1:✱3·35 -/

/- PM I (1910), p. 118, ✱3·33.  The printed `Syll.Imp` step is one
detachment.  In a nonempty real-variable context this is the printed ✱1·11;
the empty-context branch is the documented ✱1·1 relaxation. -/
/-- Audited scope reading of ✱3·33. -/
def star_3_33_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ q . q ⊃ r . ⊃ . p ⊃ r"
  parsed := ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r)
  scopeReading := "The two adjacent implications form the product antecedent; p ⊃ r is the consequent."

theorem star_3_33 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r)) := by
  have line1 : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
    PM.FirstEdition.Volume1.Star2.star_2_05 p q r
  have line2a : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_04 (q ⊃ₚ r) (p ⊃ₚ q) (p ⊃ₚ r))
  have line2 :
      ⊢ₚ (((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) ⊃ₚ
            (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r))) :=
    star_3_31 (p ⊃ₚ q) (q ⊃ₚ r) (p ⊃ₚ r)
  have line3 := PM.Derivation.detach line2a line2
  have citedImp := PM.FirstEdition.Volume1.Star2.star_2_06 p q r
  exact PM.Derivation.detach citedImp
    (PM.Derivation.detach line3
      (PM.FirstEdition.Volume1.Star2.star_2_02
        ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r)))
        (((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ r))))

/- PM I (1910), p. 118, ✱3·34.  Its one detachment has the same documented
empty-context ✱1·1 relaxation as ✱3·33. -/
/-- Audited scope reading of ✱3·34. -/
def star_3_34_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : q ⊃ r . p ⊃ q . ⊃ . p ⊃ r"
  parsed := ((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r)
  scopeReading := "The two adjacent implications form the product antecedent; p ⊃ r is the consequent."

theorem star_3_34 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r)) := by
  have line1 : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
    PM.FirstEdition.Volume1.Star2.star_2_06 p q r
  have line2a : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_04 (p ⊃ₚ q) (q ⊃ₚ r) (p ⊃ₚ r))
  have line2 :
      ⊢ₚ (((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) ⊃ₚ
            (((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r))) :=
    star_3_31 (q ⊃ₚ r) (p ⊃ₚ q) (p ⊃ₚ r)
  have line3 := PM.Derivation.detach line2a line2
  have citedImp := PM.FirstEdition.Volume1.Star2.star_2_05 p q r
  exact PM.Derivation.detach citedImp
    (PM.Derivation.detach line3
      (PM.FirstEdition.Volume1.Star2.star_2_02
        ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r)))
        (((q ⊃ₚ r) ∧ₚ (p ⊃ₚ q)) ⊃ₚ (p ⊃ₚ r))))

/- PM I (1910), p. 118, ✱3·35.  Its one detachment has the same documented
empty-context ✱1·1 relaxation as ✱3·33. -/
/-- Audited scope reading of ✱3·35. -/
def star_3_35_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . p ⊃ q . ⊃ . q"
  parsed := (p ∧ₚ (p ⊃ₚ q)) ⊃ₚ q
  scopeReading := "The product of p and p ⊃ q is the antecedent; q is the consequent."

theorem star_3_35 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ (p ⊃ₚ q)) ⊃ₚ q) := by
  have minor : ⊢ₚ (p ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)) :=
    PM.FirstEdition.Volume1.Star2.star_2_27 p q
  have major :
      ⊢ₚ ((p ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)) ⊃ₚ ((p ∧ₚ (p ⊃ₚ q)) ⊃ₚ q)) :=
    star_3_31 p (p ⊃ₚ q) q
  match Γ, p, q, minor, major with
  | [], _, _, minor, major => exact PM.Derivation.star_1_1 minor major
  | (τ :: Δ), _, _, minor, major =>
      exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) minor major

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

/-- Audited scope reading of ✱3·37. -/
def star_3_37_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . r : ⊃ : p . ∼r . ⊃ . ∼q"
  parsed := ((p ∧ₚ q) ⊃ₚ r) ⊃ₚ ((p ∧ₚ (∼ₚ r)) ⊃ₚ (∼ₚ q))
  scopeReading := "The major dots make (p . q) ⊃ r the antecedent and (p . ∼r) ⊃ ∼q the consequent."

/-- ✱3·37, following the three numbered intermediate lines in PM. -/
theorem star_3_37 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ⊃ₚ ((p ∧ₚ (∼ₚ r)) ⊃ₚ (∼ₚ q))) := by
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact PM.Derivation.detach hAB
      (PM.Derivation.detach hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have line1 : ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (p ⊃ₚ ((∼ₚ r) ⊃ₚ (∼ₚ q)))) :=
    PM.Derivation.detach
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_16 q r)
        (PM.FirstEdition.Volume1.Star2.star_2_02 p
          ((q ⊃ₚ r) ⊃ₚ ((∼ₚ r) ⊃ₚ (∼ₚ q)))))
      (PM.FirstEdition.Volume1.Star2.star_2_77 p (q ⊃ₚ r) ((∼ₚ r) ⊃ₚ (∼ₚ q)))
  have line2 : ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r))) :=
    star_3_3 p q r
  have line3 : ⊢ₚ ((p ⊃ₚ ((∼ₚ r) ⊃ₚ (∼ₚ q))) ⊃ₚ
      ((p ∧ₚ (∼ₚ r)) ⊃ₚ (∼ₚ q))) :=
    star_3_31 p (∼ₚ r) (∼ₚ q)
  exact compose (compose line2 line1) line3

/- PM-VERBATIM-BEGIN PM1:✱3·4
✱3·4.  ⊢ : p . q . ⊃ . p ⊃ q   [✱2·51 . Transp . (✱1·01 . ✱3·01)]
PM-VERBATIM-END PM1:✱3·4 -/

/-- Audited scope reading of ✱3·4. -/
def star_3_4_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . q . ⊃ . p ⊃ q"
  parsed := (p ∧ₚ q) ⊃ₚ (p ⊃ₚ q)
  scopeReading := "The product p . q is the antecedent; p ⊃ q is the consequent."

/-- ✱3·4, following the printed ✱2·51, transposition, and definitional rewrites. -/
theorem star_3_4 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ⊃ₚ (p ⊃ₚ q)) := by
  have line1 : ⊢ₚ (∼ₚ (p ⊃ₚ q) ⊃ₚ (p ⊃ₚ ∼ₚ q)) :=
    PM.FirstEdition.Volume1.Star2.star_2_51 p q
  have line2 : ⊢ₚ (∼ₚ (p ⊃ₚ ∼ₚ q) ⊃ₚ ∼ₚ (∼ₚ (p ⊃ₚ q))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_16
        (∼ₚ (p ⊃ₚ q)) (p ⊃ₚ ∼ₚ q))
  have line3 : ⊢ₚ (∼ₚ (p ⊃ₚ ∼ₚ q) ⊃ₚ (p ⊃ₚ q)) :=
    PM.Derivation.detach line2
      (PM.Derivation.detach
        (PM.FirstEdition.Volume1.Star2.star_2_14 (p ⊃ₚ q))
        (PM.FirstEdition.Volume1.Star2.star_2_05
          (∼ₚ (p ⊃ₚ ∼ₚ q)) (∼ₚ (∼ₚ (p ⊃ₚ q))) (p ⊃ₚ q)))
  rw [star_1_01 p (∼ₚ q), ← star_3_01 p q] at line3
  exact line3

/- PM-VERBATIM-BEGIN PM1:✱3·41
✱3·41.  ⊢ :. p ⊃ r . ⊃ : p . q . ⊃ . r   [✱3·26 . Syll]
PM-VERBATIM-END PM1:✱3·41 -/

/-- Audited scope reading of ✱3·41. -/
def star_3_41_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. p ⊃ r . ⊃ : p . q . ⊃ . r"
  parsed := (p ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)
  scopeReading := "The implication p ⊃ r is the antecedent; (p . q) ⊃ r is the consequent."

theorem star_3_41 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) :=
  PM.Derivation.detach (star_3_26 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_06 (p ∧ₚ q) p r)

/- PM-VERBATIM-BEGIN PM1:✱3·42
✱3·42.  ⊢ :. q ⊃ r . ⊃ : p . q . ⊃ . r   [✱3·27 . Syll]
PM-VERBATIM-END PM1:✱3·42 -/

/-- Audited scope reading of ✱3·42. -/
def star_3_42_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : p . q . ⊃ . r"
  parsed := (q ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)
  scopeReading := "The implication q ⊃ r is the antecedent; (p . q) ⊃ r is the consequent."

theorem star_3_42 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) :=
  PM.Derivation.detach (star_3_27 p q)
    (PM.FirstEdition.Volume1.Star2.star_2_06 (p ∧ₚ q) q r)

/- PM-VERBATIM-BEGIN PM1:✱3·43
✱3·43.  ⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q . r

Dem.

⊢ . ✱3·2 . ⊃ ⊢ : q . ⊃ : r . ⊃ . q . r   (1)
⊢ . (1) . Syll . ⊃ ⊢ :: p ⊃ q . ⊃ : p . ⊃ : r . ⊃ . q . r :
[✱2·77] ⊃ : p ⊃ r . ⊃ : p . ⊃ . q . r   (2)
⊢ . (2) . Imp . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱3·43 -/

/-- Audited scope reading of ✱3·43. -/
def star_3_43_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q . r"
  parsed := ((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ∧ₚ r))
  scopeReading := "The two initial implications form the product antecedent; p is the antecedent of q . r in the consequent."

/-- ✱3·43, retaining PM's two numbered lines and final importation. -/
theorem star_3_43 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ∧ₚ r))) := by
  have line1 : ⊢ₚ (q ⊃ₚ (r ⊃ₚ (q ∧ₚ r))) := star_3_2 q r
  have firstSyll : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ (r ⊃ₚ (q ∧ₚ r)))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star2.star_2_05 p q (r ⊃ₚ (q ∧ₚ r)))
  have line2 : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ∧ₚ r)))) :=
    PM.Derivation.detach firstSyll
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_77 p r (q ∧ₚ r))
        (PM.FirstEdition.Volume1.Star2.star_2_05 (p ⊃ₚ q)
          (p ⊃ₚ (r ⊃ₚ (q ∧ₚ r))) ((p ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ∧ₚ r)))))
  exact PM.Derivation.detach line2
    (star_3_31 (p ⊃ₚ q) (p ⊃ₚ r) (p ⊃ₚ (q ∧ₚ r)))

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

/- ✱3·44. -/
/-- Audited scope reading of ✱3·44. -/
def star_3_44_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : q ⊃ p . r ⊃ p . ⊃ : q ∨ r . ⊃ . p"
  parsed := ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ⊃ₚ ((q ∨ₚ r) ⊃ₚ p)
  scopeReading := "The two implications form the product antecedent; the consequent is (q ∨ r) ⊃ p."

theorem star_3_44 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ⊃ₚ ((q ∨ₚ r) ⊃ₚ p)) := by
  have syll : ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C h₁ h₂
    exact PM.Derivation.detach h₂ (PM.Derivation.detach h₁
      (PM.Derivation.detach (star_3_33 A B C)
        (star_3_3 (A ⊃ₚ B) (B ⊃ₚ C) (A ⊃ₚ C))))
  have printedSyll : ⊢ₚ ((((∼ₚ q) ⊃ₚ r) ∧ₚ (r ⊃ₚ p)) ⊃ₚ ((∼ₚ q) ⊃ₚ p)) :=
    star_3_33 (∼ₚ q) r p
  have line1 : ⊢ₚ ((((∼ₚ q) ⊃ₚ r) ∧ₚ (r ⊃ₚ p)) ⊃ₚ ((q ⊃ₚ p) ⊃ₚ p)) :=
    syll _ _ _ printedSyll (PM.FirstEdition.Volume1.Star2.star_2_6 q p)
  have exported : ⊢ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ ((r ⊃ₚ p) ⊃ₚ ((q ⊃ₚ p) ⊃ₚ p))) :=
    PM.Derivation.detach line1
      (star_3_3 ((∼ₚ q) ⊃ₚ r) (r ⊃ₚ p) ((q ⊃ₚ p) ⊃ₚ p))
  have commInner : ⊢ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ ((q ⊃ₚ p) ⊃ₚ ((r ⊃ₚ p) ⊃ₚ p))) :=
    syll _ _ _ exported (PM.FirstEdition.Volume1.Star2.star_2_04 (r ⊃ₚ p) (q ⊃ₚ p) p)
  have commOuter : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ ((r ⊃ₚ p) ⊃ₚ p))) :=
    PM.Derivation.detach commInner
      (PM.FirstEdition.Volume1.Star2.star_2_04 ((∼ₚ q) ⊃ₚ r) (q ⊃ₚ p) ((r ⊃ₚ p) ⊃ₚ p))
  have commInner₂ : ⊢ₚ ((q ⊃ₚ p) ⊃ₚ ((r ⊃ₚ p) ⊃ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ p))) :=
    syll _ _ _ commOuter (PM.FirstEdition.Volume1.Star2.star_2_04 ((∼ₚ q) ⊃ₚ r) (r ⊃ₚ p) p)
  have line2 : ⊢ₚ (((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ⊃ₚ (((∼ₚ q) ⊃ₚ r) ⊃ₚ p)) :=
    PM.Derivation.detach commInner₂
      (star_3_31 (q ⊃ₚ p) (r ⊃ₚ p) (((∼ₚ q) ⊃ₚ r) ⊃ₚ p))
  have transfer : ⊢ₚ ((((∼ₚ q) ⊃ₚ r) ⊃ₚ p) ⊃ₚ ((q ∨ₚ r) ⊃ₚ p)) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_53 q r)
      (PM.Derivation.detach (star_3_33 (q ∨ₚ r) ((∼ₚ q) ⊃ₚ r) p)
        (star_3_3 ((q ∨ₚ r) ⊃ₚ ((∼ₚ q) ⊃ₚ r)) (((∼ₚ q) ⊃ₚ r) ⊃ₚ p) ((q ∨ₚ r) ⊃ₚ p)))
  exact syll _ _ _ line2 transfer

/- ✱3·45. The two uses of ✱3·3 are the documented implicit exportations. -/
/-- Audited scope reading of ✱3·45. -/
def star_3_45_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ q . ⊃ : p . r . ⊃ . q . r"
  parsed := (p ⊃ₚ q) ⊃ₚ ((p ∧ₚ r) ⊃ₚ (q ∧ₚ r))
  scopeReading := "p ⊃ q is the outer antecedent; the consequent says p . r implies q . r."

theorem star_3_45 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((p ∧ₚ r) ⊃ₚ (q ∧ₚ r))) := by
  have printedSyll : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r)))) :=
    PM.Derivation.detach (star_3_33 p q (∼ₚ r))
      (star_3_3 (p ⊃ₚ q) (q ⊃ₚ (∼ₚ r)) (p ⊃ₚ (∼ₚ r)))
  have transp : ⊢ₚ (((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ
        ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r))))) :=
    PM.FirstEdition.Volume1.Star2.star_2_16 (q ⊃ₚ (∼ₚ r)) (p ⊃ₚ (∼ₚ r))
  have line3 := PM.Derivation.detach transp (PM.Derivation.detach printedSyll
    (PM.Derivation.detach
      (star_3_33 (p ⊃ₚ q) ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r)))
        ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r)))))
      (star_3_3 ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))))
        (((q ⊃ₚ (∼ₚ r)) ⊃ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r)))))
        ((p ⊃ₚ q) ⊃ₚ ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r))))))))
  let T : PM.Elementary Γ := (p ⊃ₚ q) ⊃ₚ ((p ∧ₚ r) ⊃ₚ (q ∧ₚ r))
  have line3eq :
      ((p ⊃ₚ q) ⊃ₚ
        ((∼ₚ (p ⊃ₚ (∼ₚ r))) ⊃ₚ (∼ₚ (q ⊃ₚ (∼ₚ r))))) = T := by
    dsimp [T]
    rw [star_1_01 p (∼ₚ r), star_1_01 q (∼ₚ r),
      star_3_01 p r, star_3_01 q r]
  have line3' : ⊢ₚ T := (congrArg PM.Derivation line3eq).mp line3
  have line4 : ⊢ₚ (T ⊃ₚ T) := PM.FirstEdition.Volume1.Star2.star_2_08 T
  exact PM.Derivation.detach line3' line4

/- ✱3·47. ✱3·2 is the documented equivalence-packaging relaxation in both
context branches; ✱3·03 remains the printed nonempty-context adjunction. -/
/-- Audited scope reading of ✱3·47. -/
def star_3_47_reading (p q r s : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ r . q ⊃ s . ⊃ : p . q . ⊃ . r . s"
  parsed := ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s))
  scopeReading := "The product of p ⊃ r and q ⊃ s is the outer antecedent; the consequent maps p . q to r . s."

theorem star_3_47 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s))) := by
  have syllOf :
      (∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B))) →
      ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro adjoin A B C h₁ h₂
    have k₁ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (A ⊃ₚ B)) := star_3_26 (A ⊃ₚ B) (B ⊃ₚ C)
    have k₂ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (B ⊃ₚ C)) := star_3_27 (A ⊃ₚ B) (B ⊃ₚ C)
    have k₃ : ⊢ₚ ((((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C))) ⊃ₚ (A ⊃ₚ C)) :=
      PM.Derivation.detach k₂ (PM.Derivation.detach k₁
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((A ⊃ₚ B) ∧ₚ (B ⊃ₚ C)) A B C))
    exact PM.Derivation.detach (adjoin _ _ h₁ h₂) k₃
  have printed :
      (∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B))) →
      (∀ W M : PM.Elementary Γ, (⊢ₚ M) → (⊢ₚ (W ⊃ₚ M))) →
      ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ s))) := by
    intro adjoin carry
    have syll := syllOf adjoin
    have first : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (p ⊃ₚ r)) := star_3_26 (p ⊃ₚ r) (q ⊃ₚ s)
    have fact₁ : ⊢ₚ ((p ⊃ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ q))) := star_3_45 p r q
    have firstFact : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (r ∧ₚ q))) :=
      syll _ _ _ first fact₁
    have perm₁ : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((r ∧ₚ q) ⊃ₚ (q ∧ₚ r))) :=
      carry _ _ (star_3_22 r q)
    have line1 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r))) :=
      PM.Derivation.detach perm₁ (PM.Derivation.detach firstFact
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (p ∧ₚ q) (r ∧ₚ q) (q ∧ₚ r)))
    have second : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (q ⊃ₚ s)) := star_3_27 (p ⊃ₚ r) (q ⊃ₚ s)
    have fact₂ : ⊢ₚ ((q ⊃ₚ s) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (s ∧ₚ r))) := star_3_45 q s r
    have secondFact : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (s ∧ₚ r))) :=
      syll _ _ _ second fact₂
    have perm₂ : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((s ∧ₚ r) ⊃ₚ (r ∧ₚ s))) :=
      carry _ _ (star_3_22 s r)
    have line2 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))) :=
      PM.Derivation.detach perm₂ (PM.Derivation.detach secondFact
        (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (q ∧ₚ r) (s ∧ₚ r) (r ∧ₚ s)))
    have joined := adjoin _ _ line1 line2
    have readBack₁ := PM.Derivation.detach joined
      (star_3_26 (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r)))
        (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))))
    have readBack₂ := PM.Derivation.detach joined
      (star_3_27 (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ r)))
        (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((q ∧ₚ r) ⊃ₚ (r ∧ₚ s))))
    exact PM.Derivation.detach readBack₂ (PM.Derivation.detach readBack₁
      (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (p ∧ₚ q) (q ∧ₚ r) (r ∧ₚ s)))
  have adjoin : ∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) :=
    fun A B hA hB => PM.Derivation.detach hB
      (PM.Derivation.detach hA (star_3_2 A B))
  exact printed adjoin fun W M hM => syllOf adjoin _ _ _
    (PM.Derivation.detach hM (star_3_2 M W)) (star_3_26 M W)

/- ✱3·48. -/
/-- Audited scope reading of ✱3·48. -/
def star_3_48_reading (p q r s : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ r . q ⊃ s . ⊃ : p ∨ q . ⊃ . r ∨ s"
  parsed := ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))
  scopeReading := "The product of p ⊃ r and q ⊃ s is the outer antecedent; the consequent maps p ∨ q to r ∨ s."

theorem star_3_48 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))) := by
  have syll : ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C h₁ h₂
    exact PM.Derivation.detach h₁ (PM.Derivation.detach h₂
      (PM.FirstEdition.Volume1.Star1.star_1_6 (∼ₚ A) B C))
  have second : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (q ⊃ₚ s)) := star_3_27 (p ⊃ₚ r) (q ⊃ₚ s)
  have propagation₁ : ⊢ₚ ((q ⊃ₚ s) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ s))) :=
    PM.FirstEdition.Volume1.Star1.star_1_6 p q s
  have secondSum : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ s))) := syll _ _ _ second propagation₁
  have perm₁ : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (s ∨ₚ p))) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star1.star_1_4 p s)
      (PM.FirstEdition.Volume1.Star1.star_1_6 (∼ₚ (p ∨ₚ q)) (p ∨ₚ s) (s ∨ₚ p))
  have line1 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (s ∨ₚ p))) := syll _ _ _ secondSum perm₁
  have first : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ (p ⊃ₚ r)) := star_3_26 (p ⊃ₚ r) (q ⊃ₚ s)
  have propagation₂ : ⊢ₚ ((p ⊃ₚ r) ⊃ₚ ((s ∨ₚ p) ⊃ₚ (s ∨ₚ r))) :=
    PM.FirstEdition.Volume1.Star1.star_1_6 s p r
  have firstSum : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((s ∨ₚ p) ⊃ₚ (s ∨ₚ r))) := syll _ _ _ first propagation₂
  have perm₂ : ⊢ₚ (((s ∨ₚ p) ⊃ₚ (s ∨ₚ r)) ⊃ₚ ((s ∨ₚ p) ⊃ₚ (r ∨ₚ s))) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star1.star_1_4 s r)
      (PM.FirstEdition.Volume1.Star1.star_1_6 (∼ₚ (s ∨ₚ p)) (s ∨ₚ r) (r ∨ₚ s))
  have line2 : ⊢ₚ (((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ⊃ₚ ((s ∨ₚ p) ⊃ₚ (r ∨ₚ s))) := syll _ _ _ firstSum perm₂
  exact PM.Derivation.detach line2 (PM.Derivation.detach line1
    (PM.FirstEdition.Volume1.Star2.star_2_83 ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) (p ∨ₚ q) (s ∨ₚ p) (r ∨ₚ s)))

end PM.FirstEdition.Volume1.Star3
