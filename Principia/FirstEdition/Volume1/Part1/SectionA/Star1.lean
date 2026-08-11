import Principia.Deduction.Formation
import Principia.Deduction.System
import Principia.Syntax.Printed

namespace PM.FirstEdition.Volume1.Star1

/-! # ✱1. Primitive Ideas and Propositions

Canonical edition: first edition, volume I (1910), pp. 95–100.
The scan is authoritative; the Project Gutenberg and Wikisource transcriptions
are independent working aids. Text between `PM-VERBATIM` markers is historical
source text, not modern editorial explanation.
-/

/- PM-VERBATIM-BEGIN PM1:PRIMITIVE-IDEAS
✱1. PRIMITIVE IDEAS AND PROPOSITIONS.

Since all definitions of terms are effected by means of other terms, every
system of definitions which is not circular must start from a certain apparatus
of undefined terms. It is to some extent optional what ideas we take as
undefined in mathematics; the motives guiding our choice will be (1) to make
the number of undefined ideas as small as possible, (2) as between two systems
in which the number is equal, to choose the one which seems the simpler and
easier. We know no way of proving that such and such a system of undefined
ideas contains as few as will give such and such results[38]. Hence we can only
say that such and such ideas are undefined in such and such a system, not that
they are indefinable. Following Peano, we shall call the undefined ideas and
the undemonstrated propositions primitive ideas and primitive propositions
respectively. The primitive ideas are explained by means of descriptions
intended to point out to the reader what is meant; but the explanations do not
constitute definitions, because they really involve the ideas they explain.

In the present number, we shall first enumerate the primitive ideas required in
this section; then we shall define implication; and then we shall enunciate the
primitive propositions required in this section. Every definition or
proposition in the work has a number, for purposes of reference. Following
Peano, we use numbers having a decimal as well as an integral part, in order to
be able to insert new propositions between any two. A change in the integral
part of the number will be used to correspond to a new chapter. Definitions
will generally have numbers whose decimal part is less than ·1, and will be
usually put at the beginning of chapters. In references, the integral parts of
the numbers of propositions will be distinguished by being preceded by a star;
thus “✱1·01” will mean the definition or proposition so numbered, and “✱1”
will mean the chapter in which propositions have numbers whose integral part
is 1, i.e. the present chapter. Chapters will generally be called “numbers.”

PRIMITIVE IDEAS.

(1) Elementary propositions. By an “elementary” proposition we mean one which
does not involve any variables, or, in other language, one which does not
involve such words as “all,” “some,” “the” or equivalents for such words. A
proposition such as “this is red,” where “this” is something given in sensation,
will be elementary. Any combination of given elementary propositions by means
of negation, disjunction or conjunction (see below) will be elementary. In the
primitive propositions of the present number, and therefore in the deductions
from these primitive propositions in ✱2—✱5, the letters p, q, r, s will be used
to denote elementary propositions.

(2) Elementary propositional functions. By an “elementary propositional
function” we shall mean an expression containing an undetermined constituent,
i.e. a variable, or several such constituents, and such that, when the
undetermined constituent or constituents are determined, i.e. when values are
assigned to the variable or variables, the resulting value of the expression in
question is an elementary proposition. Thus if p is an undetermined elementary
proposition, “not-p” is an elementary propositional function.

We shall show in ✱9 how to extend the results of this and the following numbers
(✱1—✱5) to propositions which are not elementary.

(3) Assertion. Any proposition may be either asserted or merely considered.
If I say “Caesar died,” I assert the proposition “Caesar died,” if I say
“‘Caesar died’ is a proposition,” I make a different assertion, and “Caesar
died” is no longer asserted, but merely considered. Similarly in a hypothetical
proposition, e.g. “if a = b, then b = a,” we have two unasserted propositions,
namely “a = b” and “b = a,” while what is asserted is that the first of these
implies the second. In language, we indicate when a proposition is merely
considered by “if so-and-so” or “that so-and-so” or merely by inverted commas.
In symbols, if p is a proposition, p by itself will stand for the unasserted
proposition, while the asserted proposition will be designated by

“⊢ . p.”

The sign “⊢” is called the assertion-sign[39]; it may be read “it is true that”
(although philosophically this is not exactly what it means). The dots after
the assertion-sign indicate its range; that is to say, everything following is
asserted until we reach either an equal number of dots preceding a sign of
implication or the end of the sentence. Thus “⊢ : p . ⊃ . q” means “it is true
that p implies q,” whereas “⊢ . p . ⊃ ⊢ . q” means “p is true; therefore q is
true[40].” The first of these does not necessarily involve the truth either of
p or of q, while the second involves the truth of both.

(4) Assertion of a propositional function. Besides the assertion of definite
propositions, we need what we shall call “assertion of a propositional
function.” The general notion of asserting any propositional function is not
used until ✱9, but we use at once the notion of asserting various special
elementary propositional functions.

Let φx be a propositional function whose argument is x; then we may assert φx
without assigning a value to x. This is done, for example, when the law of
identity is asserted in the form “A is A.” Here A is left undetermined, because,
however A may be determined, the result will be true. Thus when we assert φx,
leaving x undetermined, we are asserting an ambiguous value of our function.
This is only legitimate if, however the ambiguity may be determined, the result
will be true. Thus take, as an illustration, the primitive proposition ✱1·2
below, namely

“⊢ : p ∨ p . ⊃ . p,”

i.e. “‘p or p’ implies p.” Here p may be any elementary proposition: by leaving p
undetermined, we obtain an assertion which can be applied to any particular
elementary proposition. Such assertions are like the particular enunciations
in Euclid: when it is said “let ABC be an isosceles triangle; then the angles at
the base will be equal,” what is said applies to any isosceles triangle; it is
stated concerning one triangle, but not concerning a definite one. All the
assertions in the present work, with a very few exceptions, assert
propositional functions, not definite propositions.

As a matter of fact, no constant elementary proposition will occur in the
present work, or can occur in any work which employs only logical ideas. The
ideas and propositions of logic are all general: an assertion (for example)
which is true of Socrates but not of Plato, will not belong to logic[41], and
if an assertion which is true of both is to occur in logic, it must not be made
concerning either, but concerning a variable x. In order to obtain, in logic,
a definite proposition instead of a propositional function, it is necessary to
take some propositional function and assert that it is true always or
sometimes, i.e. with all possible values of the variable or with some possible
value. Thus, giving the name “individual” to whatever there is that is neither
a proposition nor a function, the proposition “every individual is identical
with itself” or the proposition “there are individuals” will be a proposition
belonging to logic. But these propositions are not elementary.

(5) Negation. If p is any proposition, the proposition “not-p,” or “p is
false,” will be represented by “∼p.” For the present, p must be an elementary
proposition.

(6) Disjunction. If p and q are any propositions, the proposition “p or q,”
i.e. “either p is true or q is true,” where the alternatives are to be not
mutually exclusive, will be represented by “p ∨ q.” This is called the
disjunction or the logical sum of p and q. Thus “∼p ∨ q” will mean “p is false
or q is true”; ∼(p ∨ q) will mean “it is false that either p or q is true,”
which is equivalent to “p and q are both false”; ∼(∼p ∨ ∼q) will mean “it is
false that either p is false or q is false,” which is equivalent to “p and q are
both true”; and so on. For the present, p and q must be elementary propositions.

The above are all the primitive ideas required in the theory of deduction.
Other primitive ideas will be introduced in Section B.

[38] The recognized methods of proving independence are not applicable, without
reserve, to fundamentals. Cf. Principles of Mathematics, § 17. What is there
said concerning primitive propositions applies with even greater force to
primitive ideas.

[39] We have adopted both the idea and the symbol of assertion from Frege.

[40] Cf. Principles of Mathematics, § 38.

[41] When we say that a proposition “belongs to logic,” we mean that it can be
expressed in terms of the primitive ideas of logic. We do not mean that logic
applies to it, for that would of course be true of any proposition.
PM-VERBATIM-END PM1:PRIMITIVE-IDEAS -/

/- PM-EDITORIAL
The passages above are primitive ideas explained in prose, not definitions or
additional axioms. This verbal-diplomatic reflow silently rejoins line-end
hyphenation and records page boundaries in metadata rather than in the canonical
body. Numeric note labels [38]–[41] replace the page-local *, † print markers.
Typography (especially italics) is a separate presentation layer. The wording,
formulae, punctuation, and scope dots were collated against scan leaves 117–120;
no error of the first-edition printing was found in this locus.
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

/- PM-VERBATIM-BEGIN PM1:✱1·4
✱1·4.  ⊢ : p ∨ q . ⊃ . q ∨ p     Pp.

This principle states that “p or q” implies “q or p.” It states the permutative
law for logical addition of propositions, and will be called the “principle of
permutation.” It will be referred to as “Perm.”
PM-VERBATIM-END PM1:✱1·4 -/

/- PM-FORMAL-GLOSS
The canonical scan reads `q ∨ p` in the consequent. Project Gutenberg's
`data-tex` reading `p ∨ p` is a digital-witness error, recorded separately in
the critical apparatus; it is not an error in PM and receives no `[sic]`.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·5
✱1·5.  ⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)     Pp.

This principle states: “If either p is true, or ‘q or r’ is true, then either q
is true, or ‘p or r’ is true.” It is a form of the associative law for logical
addition, and will be called the “associative principle.” It will be referred
to as “Assoc.” The proposition

                 p ∨ (q ∨ r) . ⊃ . (p ∨ q) ∨ r,

which would be the natural form for the associative law, has less deductive
power, and is therefore not taken as a primitive proposition.
PM-VERBATIM-END PM1:✱1·5 -/

/- PM-FORMAL-GLOSS
The displayed comparison proposition is part of PM's explanation, but it is not
the primitive proposition. The primitive consequent is `q ∨ (p ∨ r)`.
-/

/- PM-VERBATIM-BEGIN PM1:✱1·6
✱1·6.  ⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r     Pp.

This principle states: “If q implies r, then ‘p or q’ implies ‘p or r.’” In
other words, in an implication, an alternative may be added to both premiss and
conclusion without impairing the truth of the implication. The principle will
be called the “principle of summation,” and will be referred to as “Sum.”
PM-VERBATIM-END PM1:✱1·6 -/

/- PM-EDITORIAL
Sources for ✱1·4–✱1·6:
- scan, printed p. 100: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/122
- scan, printed p. 101: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/123
- working transcription: Project Gutenberg ebook 78050
Verification status: double-checked against the canonical scan and independent
digital witnesses. The apparatus records witness divergence without altering
the diplomatic text.
-/

/-- Audited scope reading of ✱1·4. -/
def star_1_4_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ q . ⊃ . q ∨ p     Pp."
  parsed := (p ∨ₚ q) ⊃ₚ (q ∨ₚ p)
  scopeReading := "The single dots delimit p ∨ q as antecedent and q ∨ p as consequent."

/-- Lean presentation of the primitive assertion ✱1·4 (`Perm`). -/
theorem star_1_4 (p q : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) :=
  PM.Derivation.star_1_4 p q

/-- Audited scope reading of ✱1·5. -/
def star_1_5_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r)     Pp."
  parsed := (p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r))
  scopeReading := "Parentheses fix the nested disjunctions; the single dots delimit the implication."

/-- Lean presentation of the primitive assertion ✱1·5 (`Assoc`). -/
theorem star_1_5 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (q ∨ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_5 p q r

/-- Audited scope reading of ✱1·6. -/
def star_1_6_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r     Pp."
  parsed := (q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))
  scopeReading := "The colon and dots group q ⊃ r as antecedent and (p ∨ q) ⊃ (p ∨ r) as consequent."

/-- Lean presentation of the primitive assertion ✱1·6 (`Sum`). -/
theorem star_1_6 (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
  PM.Derivation.star_1_6 p q r

/- PM-VERBATIM-BEGIN PM1:✱1·7
✱1·7. If p is an elementary proposition, ∼p is an elementary proposition. Pp.
PM-VERBATIM-END PM1:✱1·7 -/

/- PM-VERBATIM-BEGIN PM1:✱1·71
✱1·71. If p and q are elementary propositions, p ∨ q is an elementary proposition. Pp.
PM-VERBATIM-END PM1:✱1·71 -/

/- PM-VERBATIM-BEGIN PM1:✱1·72
✱1·72. If φp and ψp are elementary propositional functions which take
elementary propositions as arguments, φp ∨ ψp is an elementary propositional
function. Pp.
PM-VERBATIM-END PM1:✱1·72 -/

/- PM-FORMAL-GLOSS
These are primitive propositions of formation, not asserted object-language
formulae and not constructors of `PM.Derivation`. They are represented by the
three distinct constructors `PM.Formation.star_1_7`, `star_1_71`, and
`star_1_72`. The last constructor requires both functions to inhabit the same
explicit nonempty real-variable context; this is PM's axiom of identification
of type at the elementary level.
-/

def star_1_7_printed : PM.PrintedFormula :=
  PM.pmPrinted "If p is an elementary proposition, ∼p is an elementary proposition. Pp."

def star_1_71_printed : PM.PrintedFormula :=
  PM.pmPrinted "If p and q are elementary propositions, p ∨ q is an elementary proposition. Pp."

def star_1_72_printed : PM.PrintedFormula :=
  PM.pmPrinted "If φp and ψp are elementary propositional functions which take elementary propositions as arguments, φp ∨ ψp is an elementary propositional function. Pp."

/- PM-EDITORIAL
Source: first edition, volume I, printed p. 101, scan leaf 123:
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/123
Project Gutenberg 78050 agrees on all three sentences. The printed Errata to
the Introduction adds references to ✱1·7, ✱1·71 and ✱1·72 after ✱3·03 and
identifies ✱1·72 as the statement of the axiom of identification of type.
No print defect is established in these three items.
-/

end PM.FirstEdition.Volume1.Star1
