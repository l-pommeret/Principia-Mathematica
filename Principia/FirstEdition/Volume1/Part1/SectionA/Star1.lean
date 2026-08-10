import Principia.Deduction.System
import Principia.Syntax.Printed

namespace PM.FirstEdition.Volume1.Star1

/-! # ✱1. Primitive Ideas and Propositions

Canonical edition: first edition, volume I (1910), pp. 95–100.
The scan is authoritative; the Project Gutenberg and Wikisource transcriptions
are independent working aids. Text between `PM-VERBATIM` markers is historical
source text, not modern editorial explanation.
-/

/- PM-SOURCE-EXCERPT-BEGIN PM1:PRIMITIVE-IDEAS
PRIMITIVE IDEAS.

(1) Elementary propositions. By an “elementary” proposition we mean one which
does not involve any variables, or, in other language, one which does not
involve such words as “all,” “some,” “the” or equivalents for such words. A
proposition such as “this is red,” where “this” is something given in sensation,
will be elementary. Any combination of given elementary propositions by means
of negation, disjunction or conjunction (see below) will be elementary. In the
primitive propositions of the present number, and therefore in the deductions
from these primitive propositions in ✱2–✱5, the letters p, q, r, s will be used
to denote elementary propositions.

(2) Elementary propositional functions. By an “elementary propositional
function” we shall mean an expression containing an undetermined constituent,
i.e. a variable, or several such constituents, and such that, when the
undetermined constituent or constituents are determined, i.e. when values are
assigned to the variable or variables, the resulting value of the expression in
question is an elementary proposition. Thus if p is an undetermined elementary
proposition, “not-p” is an elementary propositional function.

(3) Assertion. Any proposition may be either asserted or merely considered.
If I say “Caesar died,” I assert the proposition “Caesar died,” if I say
“‘Caesar died’ is a proposition,” I make a different assertion, and “Caesar
died” is no longer asserted, but merely considered.

(4) Assertion of a propositional function. Besides the assertion of definite
propositions, we need what we shall call “assertion of a propositional
function.” The general notion of asserting any propositional function is not
used until ✱9, but we use at once the notion of asserting various special
elementary propositional functions.

(5) Negation. If p is any proposition, the proposition “not-p,” or “p is
false,” will be represented by “∼p.” For the present, p must be an elementary
proposition.

(6) Disjunction. If p and q are any propositions, the proposition “p or q,”
i.e. “either p is true or q is true,” where the alternatives are to be not
mutually exclusive, will be represented by “p ∨ q.” This is called the
disjunction or the logical sum of p and q. For the present, p and q must be
elementary propositions.
PM-SOURCE-EXCERPT-END PM1:PRIMITIVE-IDEAS -/

/- PM-EDITORIAL
The six passages above are primitive ideas explained in prose, not definitions
or additional axioms. The transcription is abbreviated within (3), (4), and
(6); it is therefore not yet the final diplomatic transcription of pp. 95–98.
Status: source-checked excerpt, incomplete surrounding prose.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·01
✱1·01.  p ⊃ q .=. ∼p ∨ q     Df.

Here the letters “Df” stand for “definition.” They and the sign of equality
together are to be regarded as forming one symbol, standing for “is defined to
mean.” Whatever comes to the left of the sign of equality is defined to mean
the same as what comes to the right of it. Definition is not among the primitive
ideas, because definitions are concerned solely with the symbolism, not with
what is symbolised; they are introduced for practical convenience, and are
theoretically unnecessary.
PM-VERBATIM-END PM1:✱1·01 -/

/- PM-FORMAL-GLOSS
`PM.Elementary.imp` is definitionally `∼p ∨ q`. The dotted `.=.` and `Df` form
a metasymbol in print; this item is not encoded as a derivable equivalence.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·1
✱1·1. Anything implied by a true elementary proposition is true. Pp.
PM-VERBATIM-END PM1:✱1·1 -/

/- PM-FORMAL-GLOSS
This is the inference constructor `PM.Derivation.star_1_1`. PM explicitly says
that it cannot be expressed symbolically here; it is not replaced by an
object-language tautology.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·11
✱1·11. When φx can be asserted, where x is a real variable, and φx ⊃ ψx can be
asserted, where x is a real variable, then ψx can be asserted, where x is a real
variable. Pp.

This principle is also to be assumed for functions of several variables.
PM-VERBATIM-END PM1:✱1·11 -/

/- PM-FORMAL-GLOSS
This is `PM.Derivation.star_1_11`, kept separate from ✱1·1 and restricted to a
nonempty real-variable context. PM later calls it the “axiom of identification
of type.”
-/

/- PM-VERBATIM-BEGIN PM1:✱1·2
✱1·2.  ⊢ : p ∨ p . ⊃ . p     Pp.

This proposition states: “If either p is true or p is true, then p is true.” It
is called the “principle of tautology,” and will be quoted by the abbreviated
title of “Taut.” It is convenient, for purposes of reference, to give names to
a few of the more important propositions; in general, propositions will be
referred to by their numbers.
PM-VERBATIM-END PM1:✱1·2 -/

/- PM-FORMAL-GLOSS
The printed assertion sign is the judgment `⊢ₚ`; it is not a formula node. The
scope punctuation parses the body as `(p ∨ p) ⊃ p`.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·3
✱1·3.  ⊢ : q . ⊃ . p ∨ q     Pp.

This principle states: “If q is true, then ‘p or q’ is true.” Thus e.g. if q is
“to-day is Wednesday” and p is “to-day is Tuesday,” the principle states: “If
to-day is Wednesday, then to-day is either Tuesday or Wednesday.” It is called
the “principle of addition,” because it states that if a proposition is true,
any alternative may be added without making it false. The principle will be
referred to as “Add.”
PM-VERBATIM-END PM1:✱1·3 -/

/- PM-EDITORIAL
Sources for this batch:
- scan, printed p. 98: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/120
- scan, printed p. 99: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/121
- scan, printed p. 100: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/122
- working transcription: Project Gutenberg ebook 78050
Two transcription witnesses agree on these five numbered items. Verification
status: single-checked against scan; independent agent cross-check completed.
-/

/-! ## Printed syntax and audited scope readings

These declarations keep PM's diplomatic surface syntax adjacent to the parsed
AST. The assertion sign remains a judgment and the scope dots remain visible in
the `printed` field; neither is silently converted into a formula constructor.
-/

/-- Diplomatic formula of ✱1·01, including the definition metasymbol. -/
def star_1_01_printed : PM.PrintedFormula :=
  PM.pmPrinted "p ⊃ q .=. ∼p ∨ q     Df."

/-- Printed prose of ✱1·1; PM supplies no symbolic formula for this rule. -/
def star_1_1_printed : PM.PrintedFormula :=
  PM.pmPrinted "Anything implied by a true elementary proposition is true. Pp."

/-- Printed metalinguistic rule ✱1·11. -/
def star_1_11_printed : PM.PrintedFormula :=
  PM.pmPrinted "When φx can be asserted, where x is a real variable, and φx ⊃ ψx can be asserted, where x is a real variable, then ψx can be asserted, where x is a real variable. Pp."

/-- Audited scope reading of ✱1·2. -/
def star_1_2_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ p . ⊃ . p     Pp."
  parsed := (p ∨ₚ p) ⊃ₚ p
  scopeReading := "The single dots delimit (p ∨ p) as the antecedent."

/-- Lean presentation of the primitive assertion ✱1·2 (`Taut`). -/
theorem star_1_2 (p : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ p) ⊃ₚ p) :=
  PM.Derivation.star_1_2 p

/-- Audited scope reading of ✱1·3. -/
def star_1_3_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : q . ⊃ . p ∨ q     Pp."
  parsed := q ⊃ₚ (p ∨ₚ q)
  scopeReading := "The single dots delimit q as antecedent; p ∨ q is consequent."

/-- Lean presentation of the primitive assertion ✱1·3 (`Add`). -/
theorem star_1_3 (p q : PM.Elementary Γ) : ⊢ₚ (q ⊃ₚ (p ∨ₚ q)) :=
  PM.Derivation.star_1_3 p q

end PM.FirstEdition.Volume1.Star1
