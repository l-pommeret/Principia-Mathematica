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

/- PM-VERBATIM-BEGIN PM1:✱2·03
✱2·03.  ⊢ : p ⊃ ∼q . ⊃ . q ⊃ ∼p

Dem.

        [Perm  ∼p, ∼q/p, q]  ⊢ : ∼p ∨ ∼q . ⊃ . ∼q ∨ ∼p       (1)
        [(1).(✱1·01)]       ⊢ : p ⊃ ∼q . ⊃ . q ⊃ ∼p
PM-VERBATIM-END PM1:✱2·03 -/

/- PM-FORMAL-GLOSS
The first demonstration line is precisely Perm (✱1·4) with its variables
replaced by `∼p` and `∼q`. The second line applies only the definitional
reading of ✱1·01 to both disjunctions. Lean parameter instantiation records
this displayed primitive instance; it is not a generic object-language
substitution rule.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·04
✱2·04.  ⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r

Dem.

        [Assoc  ∼p, ∼q/p, q]  ⊢ :. ∼p ∨ (∼q ∨ r) . ⊃ . ∼q ∨ (∼p ∨ r)       (1)
        [(1).(✱1·01)]        ⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r
PM-VERBATIM-END PM1:✱2·04 -/

/- PM-FORMAL-GLOSS
The first demonstration line is precisely Assoc (✱1·5) with its first two
variables replaced by `∼p` and `∼q`, while `r` is unchanged. The second
line changes only the notation according to ✱1·01.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·05
✱2·05.  ⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r

Dem.

        [Sum  ∼p/p]        ⊢ :. q ⊃ r . ⊃ : ∼p ∨ q . ⊃ . ∼p ∨ r       (1)
        [(1).(✱1·01)]  ⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r
PM-VERBATIM-END PM1:✱2·05 -/

/- PM-FORMAL-GLOSS
The first demonstration line is precisely Sum (✱1·6) with its first
parameter replaced by `∼p`, leaving `q` and `r` unchanged. The second line
changes only the two displayed disjunctions into the ✱1·01 implication
notation.
-/

/- PM-EDITORIAL
Source for ✱2·03–✱2·05:
- scan, printed p. 104: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126
- working transcription: Project Gutenberg ebook 78050
Verification status: double-witness-checked; the independent source and formal
audit is recorded in `reviews/Q202-review.md`. Direct collation against the
scan found no error or witness divergence affecting these items, so no `sic`,
`corr.`, or `conj.` entry is required. Fractional substitutions printed in the
demonstrations are linearized as `replacements/variables`; their order and
punctuation are preserved.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·06
✱2·06.  ⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r

Dem.

        [Comm  (q ⊃ r, p ⊃ q, p ⊃ r)/(p, q, r)]
              ⊢ :: q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r :.
                   ⊃ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r       (1)
        [✱2·05]  ⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r        (2)
        [(1).(2).✱1·11]
              ⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r

In the last line of this proof, “(1).(2).✱1·11” means that we are inferring
in accordance with ✱1·11, having before us a proposition, namely
p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r, which, by (1), is implied by
q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r, which, by (2), is true. In general, in
such cases, we shall omit the reference to ✱1·11.

The above two propositions will both be referred to as the “principle of
the syllogism” (shortened to “Syll.”), because, as will appear later, the
syllogism in Barbara is derived from them.
PM-VERBATIM-END PM1:✱2·06 -/

/- PM-FORMAL-GLOSS
Comm (✱2·04) is instantiated, in PM's printed order, with `q ⊃ₚ r`,
`p ⊃ₚ q`, and `p ⊃ₚ r`. Its antecedent is exactly ✱2·05; one use of
the proved metalinguistic bridge `PM.Derivation.detach` reconstructs the
printed `(1).(2).✱1·11` step without adding a new object-language rule.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·07
✱2·07.  ⊢ : p . ⊃ . p ∨ p                    [✱1·3  p/q]

Here we put nothing beyond “✱1·3 p/q,” because the proposition to be proved
is what ✱1·3 becomes when p is written in place of q.
PM-VERBATIM-END PM1:✱2·07 -/

/- PM-FORMAL-GLOSS
This is exactly Add (✱1·3) with both Lean parameters instantiated by `p`.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·08
✱2·08.  ⊢ . p ⊃ p

Dem.

        [✱2·05  (p ∨ p, p)/(q, r)]
              ⊢ :: p ∨ p . ⊃ . p : ⊃ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p   (1)
        [Taut]  ⊢ : p ∨ p . ⊃ . p                                   (2)
        [(1).(2).✱1·11]
              ⊢ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p                       (3)
        [2·07]  ⊢ : p . ⊃ . p ∨ p                                  (4)
        [(3).(4).✱1·11]  ⊢ . p ⊃ p
PM-VERBATIM-END PM1:✱2·08 -/

/- PM-FORMAL-GLOSS
The proof preserves PM's two detachments and their order: first Taut (✱1·2)
is detached from the displayed ✱2·05 instance, and then ✱2·07 is detached
from the resulting line (3).
-/

/- PM-VERBATIM-BEGIN PM1:✱2·1
✱2·1.   ⊢ . ∼p ∨ p                              [Id. (✱1·01)]
PM-VERBATIM-END PM1:✱2·1 -/

/- PM-FORMAL-GLOSS
This is solely the ✱1·01 definitional reading of ✱2·08: `p ⊃ₚ p` reduces
to `∼ₚ p ∨ₚ p`. It does not invoke excluded middle as a semantic principle.
-/

/- PM-EDITORIAL
Source for ✱2·06–✱2·1:
- scan, printed pp. 104–105: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126 and /127
- working witnesses: Project Gutenberg ebook 78050 and Wikisource
Verification status: double-witness-checked and collated directly against the
facsimile; the source and formal audit is recorded in `reviews/Q203-review.md`.
No authorial print error or witness divergence requiring `sic`, `corr.`, or
`conj.` was found in these four items. The parenthesized substitutions are
linearized without changing their order; physical line breaks are reflowed.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·11
✱2·11.  ⊢ . p ∨ ∼p

Dem.

        [Perm  ∼p, p/p, q]  ⊢ : ∼p ∨ p . ⊃ . p ∨ ∼p       (1)
        [(1).✱2·1.✱1·11]  ⊢ . p ∨ ∼p

This is the law of excluded middle.
PM-VERBATIM-END PM1:✱2·11 -/

/- PM-FORMAL-GLOSS
Perm (✱1·4) is instantiated with `∼p` and `p`; its consequent is detached
from ✱2·1 exactly as in the printed second line.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·12
✱2·12.  ⊢ . p ⊃ ∼(∼p)

Dem.

        [✱2·11  ∼p/p]  ⊢ . ∼p ∨ ∼(∼p)       (1)
        [(1).(✱1·01)]  ⊢ . p ⊃ ∼(∼p)
PM-VERBATIM-END PM1:✱2·12 -/

/- PM-FORMAL-GLOSS
The proof is ✱2·11 with `∼p` substituted for `p`; ✱1·01 changes only its
definitional presentation into implication notation.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·13
✱2·13.  ⊢ . p ∨ ∼{∼(∼p)}

This proposition is a lemma for ✱2·14, which, with ✱2·12, constitutes the
principle of double negation.

Dem.

        [Sum  ∼p, ∼{∼(∼p)}/q, r]
          ⊢ :. ∼p . ⊃ . ∼{∼(∼p)} : ⊃ :
               p ∨ ∼p . ⊃ . p ∨ ∼{∼(∼p)}       (1)
        [✱2·12  ∼p/p]  ⊢ : ∼p . ⊃ . ∼{∼(∼p)}       (2)
        [(1).(2).✱1·11]
          ⊢ : p ∨ ∼p . ⊃ . p ∨ ∼{∼(∼p)}       (3)
        [(3).✱2·11.✱1·11]  ⊢ : p ∨ ∼{∼(∼p)}
PM-VERBATIM-END PM1:✱2·13 -/

/- PM-FORMAL-GLOSS
Sum (✱1·6) receives the displayed three-negation term. The two subsequent
detachments use ✱2·12 at `∼p` and then ✱2·11, in the printed order.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·14
✱2·14.  ⊢ . ∼(∼p) ⊃ p

Dem.

        [Perm  ∼{∼(∼p)}/q]
          ⊢ : p ∨ ∼{∼(∼p)} . ⊃ . ∼{∼(∼p)} ∨ p       (1)
        [(1).✱2·13.✱1·11]  ⊢ : ∼{∼(∼p)} ∨ p       (2)
        [(2).(✱1·01)]  ⊢ : ∼(∼p) ⊃ p
PM-VERBATIM-END PM1:✱2·14 -/

/- PM-FORMAL-GLOSS
Perm (✱1·4) exchanges `p` and `∼{∼(∼p)}`; detachment against ✱2·13 gives
the disjunction which ✱1·01 reads definitionally as the asserted implication.
-/

/- PM-EDITORIAL
Source for ✱2·11–✱2·14:
- scan, printed pp. 105–106: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/127 and /128
- working transcription: Project Gutenberg ebook 78050
Verification status: double-witness-checked and collated directly against the
facsimile; the source and formal audit is recorded in `reviews/Q204-review.md`.
In the first demonstration line of ✱2·13, Gutenberg's `data-tex` concatenates
the two numerator expressions. The comma above follows the scan and repairs
only that digital-witness error; it is not an emendation of PM. No `sic`,
`corr.`, or `conj.` entry concerning the printed edition is required.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·15
✱2·15.  ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ p

Dem.

 [✱2·05  (∼p, ∼(∼q))/(p, r)]
      ⊢ :. q ⊃ ∼(∼q) . ⊃ : ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q)          (1)
 [✱2·12  q/p]  ⊢ . q ⊃ ∼(∼q)                                (2)
 [(1).(2).✱1·11]
      ⊢ : ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q)                           (3)
 [✱2·03  (∼p, ∼q)/(p, q)]
      ⊢ : ∼p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼(∼p)                       (4)
 [✱2·05  (∼q, ∼(∼p), p)/(p, q, r)]
      ⊢ :. ∼(∼p) ⊃ p . ⊃ : ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p          (5)
 [(5).✱2·14.✱1·11]
      ⊢ : ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p                           (6)
 [✱2·05  (∼p ⊃ q, ∼p ⊃ ∼(∼q), ∼q ⊃ ∼(∼p))/(p, q, r)]
      ⊢ :: ∼p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :.
             ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                       (7)
 [(4).(7).✱1·11]
      ⊢ :. ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                       (8)
 [(3).(8).✱1·11]
      ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                           (9)
 [✱2·05  (∼p ⊃ q, ∼q ⊃ ∼(∼p), ∼q ⊃ p)/(p, q, r)]
      ⊢ :: ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p : ⊃ :.
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ p                            (10)
 [(6).(10).✱1·11]
      ⊢ :. ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ p                            (11)
 [(9).(11).✱1·11]  ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ p

Note on the proof of ✱2·15. In the above proof, it will be seen that (3),
(4), (6) are respectively of the forms p₁ ⊃ p₂, p₂ ⊃ p₃, p₃ ⊃ p₄, where
p₁ ⊃ p₄ is the proposition to be proved. From p₁ ⊃ p₂, p₂ ⊃ p₃, p₃ ⊃ p₄
the proposition p₁ ⊃ p₄ results by repeated applications of ✱2·05 or ✱2·06
(both of which are called “Syll.”). It is tedious and unnecessary to repeat
this process every time it is used; it will therefore be abbreviated into
“[Syll.] ⊢ .(a).(b).(c). ⊃ ⊢ .(d),” where (a) is of the form p₁ ⊃ p₂, (b)
of the form p₂ ⊃ p₃, (c) of the form p₃ ⊃ p₄, and (d) of the form p₁ ⊃ p₄.
The same abbreviation will be applied to a sorites of any length. Also where
we have “⊢ .p₁ .⊃ [etc.] ⊢ .p₂,” and p₂ is the proposition to be proved, it
is convenient to write simply “⊢ .p₁ .⊃ [etc.] ⊢ .p₂,” where “etc.” will be
a reference to the previous propositions in virtue of which the implication
p₁ ⊃ p₂ holds. This form embodies the use of ✱1·11 or ✱1·1, and makes many
proofs at once shorter and easier to follow. It is used in the first two lines
of the following proof.
PM-VERBATIM-END PM1:✱2·15 -/

/- PM-VERBATIM-BEGIN PM1:✱2·16
✱2·16.  ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p

Dem.

 [✱2·12]  ⊢ . q ⊃ ∼(∼q) . ⊃
 [✱2·05]  ⊢ : p ⊃ q . ⊃ . p ⊃ ∼(∼q)                         (1)
 [✱2·03  ∼q/q]
           ⊢ : p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼p                     (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p

Note. The proposition to be proved will be called “Prop,” and when a proof
ends, like that of ✱2·16, by an implication between asserted propositions, of
which the consequent is the proposition to be proved, we shall write
“⊢ .etc. ⊃ ⊢ .Prop”. Thus “⊃ ⊢ .Prop” ends a proof, and more or less
corresponds to “q.e.d.”
PM-VERBATIM-END PM1:✱2·16 -/

/- PM-VERBATIM-BEGIN PM1:✱2·17
✱2·17.  ⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ q

Dem.

 [✱2·03  (∼q, p)/(p, q)]
           ⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ ∼(∼q)                     (1)
 [✱2·14]  ⊢ : ∼(∼q) ⊃ q : ⊃
 [✱2·05]  ⊢ : p ⊃ ∼(∼q) . ⊃ . p ⊃ q                        (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ .Prop

✱2·15, ✱2·16 and ✱2·17 are forms of the principle of transposition, and
will be all referred to as “Transp.”
PM-VERBATIM-END PM1:✱2·17 -/

/- PM-VERBATIM-BEGIN PM1:✱2·18
✱2·18.  ⊢ : ∼p ⊃ p . ⊃ . p

Dem.

 [✱2·12]  ⊢ . p ⊃ ∼(∼p) . ⊃
 [✱2·05]  ⊢ . ∼p ⊃ p . ⊃ . ∼p ⊃ ∼(∼p)                      (1)
 [✱2·01  ∼p/p]
           ⊢ : ∼p ⊃ ∼(∼p) . ⊃ . ∼(∼p)                     (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ : ∼p ⊃ p . ⊃ . ∼(∼p)            (3)
 [✱2·14]  ⊢ . ∼(∼p) ⊃ p                                   (4)
 [Syll.]   ⊢ .(3).(4). ⊃ ⊢ .Prop

This is the complement of the principle of the reductio ad absurdum. It
states that a proposition which follows from the hypothesis of its own
falsehood is true.
PM-VERBATIM-END PM1:✱2·18 -/

/- PM-FORMAL-GLOSS
The four proofs preserve every displayed PM step. The long demonstration of
✱2·15 is retained rather than replaced by the later abbreviation Transp.;
each Syll. in ✱2·16–✱2·18 is expanded through ✱2·06 and detachment.
-/

/- PM-EDITORIAL
Source for ✱2·15–✱2·18:
- scan, printed pp. 106–108: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/128 through /130
- working witnesses: Project Gutenberg ebook 78050 and Wikisource
Verification status: double-witness-checked and collated directly against the
facsimile; the source and formal audit is recorded in `reviews/Q205-review.md`.
The four divergences recorded there are errors of the Gutenberg digital
witness, not of the 1910 impression; no `sic`, `corr.`, or `conj.` is attached.
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

/-- Audited scope reading of ✱2·03. -/
def star_2_03_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ ∼q . ⊃ . q ⊃ ∼p"
  parsed := (p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ ∼ₚ p)
  scopeReading := "The single dots delimit p ⊃ ∼q as antecedent and q ⊃ ∼p as consequent."

/-- Diplomatic surface syntax of the two-line printed demonstration of ✱2·03. -/
def star_2_03_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm  ∼p, ∼q/p, q] ⊢ : ∼p ∨ ∼q . ⊃ . ∼q ∨ ∼p; [(1).(✱1·01)] ⊢ : p ⊃ ∼q . ⊃ . q ⊃ ∼p"

/-- ✱2·03, exactly the instance of Perm specified in PM's demonstration. -/
theorem star_2_03 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ ∼ₚ p)) :=
  PM.Derivation.star_1_4 (∼ₚ p) (∼ₚ q)

/-- Audited scope reading of ✱2·04. -/
def star_2_04_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r"
  parsed := (p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r))
  scopeReading := "The colon groups p ⊃ (q ⊃ r) as antecedent and q ⊃ (p ⊃ r) as consequent."

/-- Diplomatic surface syntax of the two-line printed demonstration of ✱2·04. -/
def star_2_04_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Assoc  ∼p, ∼q/p, q] ⊢ :. ∼p ∨ (∼q ∨ r) . ⊃ . ∼q ∨ (∼p ∨ r); [(1).(✱1·01)] ⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r"

/-- ✱2·04, exactly the instance of Assoc specified in PM's demonstration. -/
theorem star_2_04 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_5 (∼ₚ p) (∼ₚ q) r

/-- Audited scope reading of ✱2·05. -/
def star_2_05_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r"
  parsed := (q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))
  scopeReading := "The dots and colons group q ⊃ r as the outer antecedent and (p ⊃ q) ⊃ (p ⊃ r) as consequent."

/-- Diplomatic surface syntax of the two-line printed demonstration of ✱2·05. -/
def star_2_05_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Sum  ∼p/p] ⊢ :. q ⊃ r . ⊃ : ∼p ∨ q . ⊃ . ∼p ∨ r; [(1).(✱1·01)] ⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r"

/-- ✱2·05, exactly the instance of Sum specified in PM's demonstration. -/
theorem star_2_05 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.star_1_6 (∼ₚ p) q r

/-- Audited scope reading of ✱2·06. -/
def star_2_06_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r"
  parsed := (p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))
  scopeReading := "The outer colon groups p ⊃ q as antecedent and (q ⊃ r) ⊃ (p ⊃ r) as consequent."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·06. -/
def star_2_06_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Comm (q ⊃ r, p ⊃ q, p ⊃ r)/(p, q, r)] (1); [✱2·05] (2); [(1).(2).✱1·11]"

/-- PM ✱2·06 (`Syll.`), with the exact printed Comm instance followed by detachment. -/
theorem star_2_06 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
  PM.Derivation.detach (star_2_05 p q r)
    (star_2_04 (q ⊃ₚ r) (p ⊃ₚ q) (p ⊃ₚ r))

/-- Audited scope reading of ✱2·07. -/
def star_2_07_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ⊃ . p ∨ p"
  parsed := p ⊃ₚ (p ∨ₚ p)
  scopeReading := "The single dots delimit p as antecedent and p ∨ p as consequent."

/-- Diplomatic surface syntax of the printed one-line proof of ✱2·07. -/
def star_2_07_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱1·3  p/q]"

/-- PM ✱2·07, the direct Add instance `p/q`. -/
theorem star_2_07 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (p ∨ₚ p)) :=
  PM.Derivation.star_1_3 p p

/-- Audited scope reading of ✱2·08. -/
def star_2_08_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ⊃ p"
  parsed := p ⊃ₚ p
  scopeReading := "The formula is the implication p ⊃ p."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·08. -/
def star_2_08_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·05 (p ∨ p, p)/(q, r)] (1); [Taut] (2); [(1).(2).✱1·11] (3); [2·07] (4); [(3).(4).✱1·11]"

/-- PM ✱2·08 (`Id.`), preserving the two printed detachments in order. -/
theorem star_2_08 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ p) :=
  PM.Derivation.detach (star_2_07 p)
    (PM.Derivation.detach (PM.Derivation.star_1_2 p)
      (star_2_05 p (p ∨ₚ p) p))

/-- Audited scope reading of ✱2·1. -/
def star_2_1_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . ∼p ∨ p"
  parsed := ∼ₚ p ∨ₚ p
  scopeReading := "By ✱1·01 this is the definitional reading of p ⊃ p."

/-- Diplomatic surface syntax of the printed one-line proof of ✱2·1. -/
def star_2_1_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Id. (✱1·01)]"

/-- PM ✱2·1, obtained only by the ✱1·01 definitional reading of ✱2·08. -/
theorem star_2_1 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ p ∨ₚ p) :=
  star_2_08 p

/-- Audited scope reading of ✱2·11. -/
def star_2_11_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ∨ ∼p"
  parsed := p ∨ₚ ∼ₚ p
  scopeReading := "The assertion is the disjunction p ∨ ∼p."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·11. -/
def star_2_11_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm ∼p, p/p, q] (1); [(1).✱2·1.✱1·11]"

/-- PM ✱2·11, preserving its Perm instance and printed detachment. -/
theorem star_2_11 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ p) := by
  have hperm := PM.Derivation.star_1_4 (∼ₚ p) p
  exact PM.Derivation.detach (star_2_1 p) hperm

/-- Audited scope reading of ✱2·12. -/
def star_2_12_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ⊃ ∼(∼p)"
  parsed := p ⊃ₚ ∼ₚ (∼ₚ p)
  scopeReading := "The consequent contains exactly two iterated negations."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·12. -/
def star_2_12_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·11 ∼p/p] (1); [(1).(✱1·01)]"

/-- PM ✱2·12, definitionally the indicated ✱2·11 instance. -/
theorem star_2_12 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ ∼ₚ (∼ₚ p)) := by
  exact star_2_11 (∼ₚ p)

/-- Audited scope reading of ✱2·13. -/
def star_2_13_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ∨ ∼{∼(∼p)}"
  parsed := p ∨ₚ ∼ₚ (∼ₚ (∼ₚ p))
  scopeReading := "The second disjunct contains exactly three iterated negations."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·13. -/
def star_2_13_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Sum ∼p, ∼{∼(∼p)}/q, r] (1); [✱2·12 ∼p/p] (2); [(1).(2).✱1·11] (3); [(3).✱2·11.✱1·11]"

/-- PM ✱2·13, preserving the Sum instance and both printed detachments. -/
theorem star_2_13 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ∼ₚ (∼ₚ (∼ₚ p))) := by
  have hsum := PM.Derivation.star_1_6 p (∼ₚ p) (∼ₚ (∼ₚ (∼ₚ p)))
  have hstep := PM.Derivation.detach (star_2_12 (∼ₚ p)) hsum
  exact PM.Derivation.detach (star_2_11 p) hstep

/-- Audited scope reading of ✱2·14. -/
def star_2_14_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . ∼(∼p) ⊃ p"
  parsed := ∼ₚ (∼ₚ p) ⊃ₚ p
  scopeReading := "The antecedent is the double negation of p."

/-- Diplomatic surface syntax of the printed demonstration of ✱2·14. -/
def star_2_14_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm ∼{∼(∼p)}/q] (1); [(1).✱2·13.✱1·11] (2); [(2).(✱1·01)]"

/-- PM ✱2·14, preserving the displayed Perm instance and detachment. -/
theorem star_2_14 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ (∼ₚ p) ⊃ₚ p) := by
  have hperm := PM.Derivation.star_1_4 p (∼ₚ (∼ₚ (∼ₚ p)))
  exact PM.Derivation.detach (star_2_13 p) hperm

/-- Audited scope reading of ✱2·15. -/
def star_2_15_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ p"
  parsed := (∼ₚ p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p)
  scopeReading := "The dot hierarchy groups the two displayed implications as antecedent and consequent."

def star_2_15_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "✱2·05 (1); ✱2·12 (2); detach (3); ✱2·03 (4); ✱2·05 (5); detach (6); ✱2·05 (7); detach (8),(9); ✱2·05 (10); detach (11), Prop"

/-- PM ✱2·15, retaining the complete printed eleven-line sorites. -/
theorem star_2_15 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p)) := by
  have line1 := star_2_05 (∼ₚ p) q (∼ₚ (∼ₚ q))
  have line2 := star_2_12 q
  have line3 := PM.Derivation.detach line2 line1
  have line4 := star_2_03 (∼ₚ p) (∼ₚ q)
  have line5 := star_2_05 (∼ₚ q) (∼ₚ (∼ₚ p)) p
  have line6 := PM.Derivation.detach (star_2_14 p) line5
  have line7 := star_2_05 (∼ₚ p ⊃ₚ q) (∼ₚ p ⊃ₚ ∼ₚ (∼ₚ q))
    (∼ₚ q ⊃ₚ ∼ₚ (∼ₚ p))
  have line8 := PM.Derivation.detach line4 line7
  have line9 := PM.Derivation.detach line3 line8
  have line10 := star_2_05 (∼ₚ p ⊃ₚ q) (∼ₚ q ⊃ₚ ∼ₚ (∼ₚ p)) (∼ₚ q ⊃ₚ p)
  have line11 := PM.Derivation.detach line6 line10
  exact PM.Derivation.detach line9 line11

/-- Audited scope reading of ✱2·16. -/
def star_2_16_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p"
  parsed := (p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p)
  scopeReading := "The proposition is the first displayed form of Transp."

def star_2_16_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·12] ⊃ [✱2·05] (1); [✱2·03 ∼q/q] (2); [Syll.] ⊢ .(1).(2). ⊃ ⊢ .Prop"

theorem star_2_16 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p)) := by
  have line1 := PM.Derivation.detach (star_2_12 q)
    (star_2_05 p q (∼ₚ (∼ₚ q)))
  have line2 := star_2_03 p (∼ₚ q)
  have syll := PM.Derivation.detach line1
    (star_2_06 (p ⊃ₚ q) (p ⊃ₚ ∼ₚ (∼ₚ q)) (∼ₚ q ⊃ₚ ∼ₚ p))
  exact PM.Derivation.detach line2 syll

/-- Audited scope reading of ✱2·17. -/
def star_2_17_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ q"
  parsed := (∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q)
  scopeReading := "The proposition is the converse transposition form."

def star_2_17_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·03 (∼q, p)/(p, q)] (1); [✱2·14] ⊃ [✱2·05] (2); [Syll.] ⊢ .Prop"

theorem star_2_17 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q)) := by
  have line1 := star_2_03 (∼ₚ q) p
  have line2 := PM.Derivation.detach (star_2_14 q)
    (star_2_05 p (∼ₚ (∼ₚ q)) q)
  have syll := PM.Derivation.detach line1
    (star_2_06 (∼ₚ q ⊃ₚ ∼ₚ p) (p ⊃ₚ ∼ₚ (∼ₚ q)) (p ⊃ₚ q))
  exact PM.Derivation.detach line2 syll

/-- Audited scope reading of ✱2·18. -/
def star_2_18_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼p ⊃ p . ⊃ . p"
  parsed := (∼ₚ p ⊃ₚ p) ⊃ₚ p
  scopeReading := "The antecedent is ∼p ⊃ p and the consequent is p."

def star_2_18_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·12] ⊃ [✱2·05] (1); [✱2·01 ∼p/p] (2); [Syll.] (3); [✱2·14] (4); [Syll.] ⊢ .Prop"

theorem star_2_18 {Γ : PM.RealContext} (p : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p ⊃ₚ p) ⊃ₚ p) := by
  have line1 := PM.Derivation.detach (star_2_12 p)
    (star_2_05 (∼ₚ p) p (∼ₚ (∼ₚ p)))
  have line2 := star_2_01 (∼ₚ p)
  have syll1 := PM.Derivation.detach line1
    (star_2_06 (∼ₚ p ⊃ₚ p) (∼ₚ p ⊃ₚ ∼ₚ (∼ₚ p)) (∼ₚ (∼ₚ p)))
  have line3 := PM.Derivation.detach line2 syll1
  have line4 := star_2_14 p
  have syll2 := PM.Derivation.detach line3
    (star_2_06 (∼ₚ p ⊃ₚ p) (∼ₚ (∼ₚ p)) p)
  exact PM.Derivation.detach line4 syll2

/- PM-VERBATIM-BEGIN PM1:✱2·33
✱2·33.  p ∨ q ∨ r .=. (p ∨ q) ∨ r     Df

This definition serves only for the avoidance of brackets.
PM-VERBATIM-END PM1:✱2·33 -/

/- PM-FORMAL-GLOSS
✱2·33 is a metalinguistic convention for reading an unbracketed chain, not an
asserted equivalence and not an associativity theorem. Accordingly `∨ₚ` is
left-associative in Lean: `p ∨ₚ q ∨ₚ r` elaborates directly to
`(p ∨ₚ q) ∨ₚ r`. Earlier PM formulae keep their printed parentheses, so
this notation declaration changes none of their audited abstract syntax trees.
-/

/- PM-EDITORIAL
Source for ✱2·33:
- scan, printed p. 110: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/132
- working transcription: Project Gutenberg ebook 78050
Verification status: scan-collated against two independent digital witnesses.
All three witnesses agree on the left-associated definiens and on the following
sentence. No `sic`, `corr.`, or `conj.` entry is required.
-/

/-- Audited definitional reading of PM's bracket-avoidance convention ✱2·33. -/
def star_2_33_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "p ∨ q ∨ r .=. (p ∨ q) ∨ r     Df"
  parsed := p ∨ₚ q ∨ₚ r
  scopeReading := "The unbracketed chain associates to the left: (p ∨ q) ∨ r."

/-- ✱2·33 as a Lean abbreviation; this introduces no object-language connective. -/
abbrev star_2_33 (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  p ∨ₚ q ∨ₚ r

end PM.FirstEdition.Volume1.Star2
