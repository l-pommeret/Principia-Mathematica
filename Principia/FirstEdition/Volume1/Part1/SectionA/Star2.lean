import Principia.Deduction.System
import Principia.Syntax.Printed

namespace PM.FirstEdition.Volume1.Star2

/-! # ✱2. Immediate Consequences of the Primitive Propositions

Canonical edition: first edition, volume I (1910), p. 104.
The scan is authoritative; the Project Gutenberg and Wikisource transcriptions
are independent working aids. Text between `PM-VERBATIM` markers is historical
source text, including the demonstrations printed by Whitehead and Russell.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·01
✱2·01.  ⊢ : p ⊃ ∼p . ⊃ . ∼p

This proposition states that, if p implies its own falsehood, then p is false.
It is called the “principle of the reductio ad absurdum,” and will be referred
to as “Abs.”* The proof is as follows (where “Dem.” is short for
demonstration”):

Dem.

        [Taut  ∼p/p]       ⊢ : ∼p ∨ ∼p . ⊃ . ∼p          (1)
        [(1).(✱1·01)]      ⊢ : p ⊃ ∼p . ⊃ . ∼p

* There is an interesting historical article on this principle by Vailati,
“A proposito d’un passo del Teeteto e di una dimostrazione di Euclide,” Rivista
di Filosofia e scienze affine, 1904.
PM-VERBATIM-END PM1:✱2·01 -/

/- PM-FORMAL-GLOSS
The first demonstration line is the schema instance `Taut [∼p/p]`, represented
by applying `PM.Derivation.star_1_2` to `∼ₚ p`. The second line changes only the
notation: by ✱1·01, `p ⊃ ∼p` is definitionally `∼p ∨ ∼p`. No object-language
substitution rule or semantic interpretation is added.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·02
✱2·02.  ⊢ : q . ⊃ . p ⊃ q

Dem.

        [Add  ∼p/p]        ⊢ : q . ⊃ . ∼p ∨ q            (1)
        [(1).(✱1·01)]      ⊢ : q . ⊃ . p ⊃ q
PM-VERBATIM-END PM1:✱2·02 -/

/- PM-FORMAL-GLOSS
The first demonstration line is the schema instance `Add [∼p/p]`, represented
by applying `PM.Derivation.star_1_3` with first argument `∼ₚ p`. The final line
is the definitional reading of ✱1·01: `p ⊃ q` is `∼p ∨ q`.
-/

/- PM-EDITORIAL
Source for both items:
- scan, printed p. 104: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126
- working transcription: Project Gutenberg ebook 78050
Verification status: double-witness-checked; independent source and formal
audits are recorded in `reviews/Q201-review.md`. The printed asterisk linking
the footnote to “Abs.” is preserved, with its note adjacent to ✱2·01. Physical
line breaks are editorially reflowed: the scan's line-end `demon-` / following
line `stration”):` is transcribed as `demonstration”):`, preserving its unusual
closing quotation mark and punctuation without treating the line-end hyphen as
lexical.
-/

/-! ## Printed syntax and audited scope readings -/

/-- Audited scope reading of ✱2·01. -/
def star_2_01_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ ∼p . ⊃ . ∼p"
  parsed := (p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p
  scopeReading := "The single dots delimit p ⊃ ∼p as antecedent; ∼p is consequent."

/-- Diplomatic surface syntax of the two-line printed demonstration of ✱2·01. -/
def star_2_01_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Taut  ∼p/p] ⊢ : ∼p ∨ ∼p . ⊃ . ∼p; [(1).(✱1·01)] ⊢ : p ⊃ ∼p . ⊃ . ∼p"

/-- ✱2·01 (`Abs`), exactly the instance of Taut specified in PM's demonstration. -/
theorem star_2_01 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ ∼ₚ p) ⊃ₚ ∼ₚ p) :=
  PM.Derivation.star_1_2 (∼ₚ p)

/-- Audited scope reading of ✱2·02. -/
def star_2_02_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : q . ⊃ . p ⊃ q"
  parsed := q ⊃ₚ (p ⊃ₚ q)
  scopeReading := "The single dots delimit q as antecedent; p ⊃ q is consequent."

/-- Diplomatic surface syntax of the two-line printed demonstration of ✱2·02. -/
def star_2_02_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Add  ∼p/p] ⊢ : q . ⊃ . ∼p ∨ q; [(1).(✱1·01)] ⊢ : q . ⊃ . p ⊃ q"

/-- ✱2·02, exactly the instance of Add specified in PM's demonstration. -/
theorem star_2_02 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ⊃ₚ q)) :=
  PM.Derivation.star_1_3 (∼ₚ p) q

end PM.FirstEdition.Volume1.Star2
