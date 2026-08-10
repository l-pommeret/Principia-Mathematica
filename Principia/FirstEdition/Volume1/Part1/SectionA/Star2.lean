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

/- PM-VERBATIM-BEGIN PM1:✱2·2
✱2·2.   ⊢ : p . ⊃ . p ∨ q

Dem.

        ⊢ . Add . ⊃ ⊢ : p . ⊃ . q ∨ p                 (1)
        [Perm] ⊢ : q ∨ p . ⊃ . p ∨ q                    (2)
        [Syll.] ⊢ .(1).(2). ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱2·2 -/

/- PM-FORMAL-GLOSS
The three printed stages are retained literally. `Add` is ✱1·3, `Perm` is
✱1·4, and the displayed `Syll.` is expanded with ✱2·05 and two uses of
the proved metalinguistic detachment bridge.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·21
✱2·21.  ⊢ : ∼p . ⊃ . p ⊃ q                    [✱2·2  ∼p/p]

The above two propositions are very frequently used.
PM-VERBATIM-END PM1:✱2·21 -/

/- PM-FORMAL-GLOSS
This is exactly the displayed instance of ✱2·2 with `∼p` in place of `p`;
the inner disjunction is merely read as implication by ✱1·01.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·24
✱2·24.  ⊢ : p . ⊃ . ∼p ⊃ q                    [✱2·21.Comm]
PM-VERBATIM-END PM1:✱2·24 -/

/- PM-FORMAL-GLOSS
`Comm` is ✱2·04 instantiated so that its antecedent is the exact result
✱2·21; detachment gives the printed consequent.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·25
✱2·25.  ⊢ :· p : ∨ : p ∨ q . ⊃ . q

Dem.

        ⊢ . ✱2·1 . ⊃ ⊢ : ∼(p ∨ q) . ∨ . (p ∨ q) :
        [Assoc.]  ⊃ ⊢ : p . ∨ . {∼(p ∨ q) . ∨ . q} : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱2·25 -/

/- PM-FORMAL-GLOSS
The colon-and-dot scope has abstract syntax `p ∨ ((p ∨ q) ⊃ q)`, not
`(p ∨ (p ∨ q)) ⊃ q`. The proof instantiates ✱2·1 at `p ∨ q`, then
uses Assoc (✱1·5) and detachment exactly as printed.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·26
✱2·26.  ⊢ :· ∼p : ∨ : p ⊃ q . ⊃ . q                    [✱2·25  ∼p/p]
PM-VERBATIM-END PM1:✱2·26 -/

/- PM-FORMAL-GLOSS
This is the displayed substitution instance of ✱2·25; implication is reduced
only according to ✱1·01.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·27
✱2·27.  ⊢ :· p . ⊃ : p ⊃ q . ⊃ . q                    [✱2·26]
PM-VERBATIM-END PM1:✱2·27 -/

/- PM-FORMAL-GLOSS
This is solely the ✱1·01 reading of ✱2·26; it adds no inference step.
-/

/- PM-EDITORIAL
Source for ✱2·2, ✱2·21 and ✱2·24–✱2·27:
- scan, printed pp. 108–109: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/130 and /131
- working witnesses: Project Gutenberg ebook 78050 and Wikisource
Verification status: double-witness-checked and collated directly against the
facsimile; the independent formal audits are recorded in
`reviews/Q206-review.md` and `reviews/Q207-review.md`. No authorial print error
or digital-witness divergence requiring `sic`, `corr.`, or `conj.` was found.
Fractional substitutions are linearized as `replacement/variable`, preserving
their printed order; physical line breaks are reflowed.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·3
✱2·3.  ⊢ : p ∨ (q ∨ r) . ⊃ . p ∨ (r ∨ q)

Dem.

        [Perm  (q, r)/(p, q)]
              ⊢ : q ∨ r . ⊃ . r ∨ q :
        [Sum  (q ∨ r, r ∨ q)/(q, r)] ⊃
              ⊢ : p ∨ (q ∨ r) . ⊃ . p ∨ (r ∨ q)
PM-VERBATIM-END PM1:✱2·3 -/

/- PM-VERBATIM-BEGIN PM1:✱2·31
✱2·31.  ⊢ : p ∨ (q ∨ r) . ⊃ . (p ∨ q) ∨ r

This proposition and ✱2·32 together constitute the associative law for
logical addition of propositions. In the proof, the following abbreviation
(constantly used hereafter) will be employed*: When we have a series of
propositions of the form a ⊃ b, b ⊃ c, c ⊃ d, all asserted, and
“a ⊃ d” is the proposition to be proved, the proof in full is as follows:

        [Syll.]  ⊢ :. a ⊃ b . ⊃ : b ⊃ c . ⊃ . a ⊃ c       (1)
                 ⊢ : a . ⊃ . b                                  (2)
        [(1).(2).✱1·11]
                 ⊢ : b ⊃ c . ⊃ . a ⊃ c                       (3)
                 ⊢ : b . ⊃ . c                                  (4)
        [(3).(4).✱1·11]
                 ⊢ : a . ⊃ . c                                  (5)
        [Syll.]  ⊢ :. a ⊃ c . ⊃ : c ⊃ d . ⊃ . a ⊃ d       (6)
        [(5).(6).✱1·11]
                 ⊢ : c ⊃ d . ⊃ . a ⊃ d                       (7)
                 ⊢ : c . ⊃ . d                                  (8)
        [(7).(8).✱1·11]
                 ⊢ : a . ⊃ . d

It is tedious to write out this process in full; we therefore write simply

                 ⊢ : a . ⊃ . b .
        [etc.]          ⊃ . c .
        [etc.]          ⊃ . d : ⊃ ⊢ . Prop,

where “a ⊃ d” is the proposition to be proved. We indicate on the left by
references in square brackets the propositions in virtue of which the
successive implications hold. We put one dot (not two) after “b,” to show
that it is b, not “a ⊃ b,” that implies c. But we put two dots after d, to
show that now the whole proposition “a ⊃ d” is concerned. If “a ⊃ d” is not
the proposition to be proved, but is to be used subsequently in the proof,
we put

                 ⊢ : a . ⊃ . b .
        [etc.]          ⊃ . c .
        [etc.]          ⊃ . d                                  (1),

and then “(1)” means “a ⊃ d.” The proof of ✱2·31 is as follows:

Dem.

        [✱2·3]  ⊢ : p ∨ (q ∨ r) .
                    ⊃ . p ∨ (r ∨ q) .
        [Assoc  (r, q)/(q, r)]
                    ⊃ . r ∨ (p ∨ q) .
        [Perm  (r, p ∨ q)/(p, q)]
                    ⊃ . (p ∨ q) ∨ r : ⊃ ⊢ . Prop

* This abbreviation applies to the same type of cases as those concerned in
the note to ✱2·15, but is often more convenient than the abbreviation explained
in that note.
PM-VERBATIM-END PM1:✱2·31 -/

/- PM-VERBATIM-BEGIN PM1:✱2·32
✱2·32.  ⊢ : (p ∨ q) ∨ r . ⊃ . p ∨ (q ∨ r)

Dem.

        [Perm  (p ∨ q, r)/(p, q)]
              ⊢ : (p ∨ q) ∨ r . ⊃ . r ∨ (p ∨ q)
        [Assoc  (r, p, q)/(p, q, r)]
                    ⊃ . p ∨ (r ∨ q)
        [✱2·3]      ⊃ . p ∨ (q ∨ r) : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱2·32 -/

/- PM-FORMAL-GLOSS
In ✱2·3, Perm is raised by Sum and detached exactly as displayed. The long
note preceding ✱2·31 defines PM's sorites abbreviation by expanding it into
Syll. and ✱1·11; the Lean proofs of ✱2·31 and ✱2·32 retain that expansion
through exact ✱2·05 instances and `PM.Derivation.detach`. No generic composition
lemma replaces the printed reasoning.
-/

/- PM-EDITORIAL
Source for ✱2·3, ✱2·31 and ✱2·32:
- scan, printed pp. 109–110: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/131 and /132
- working witnesses: Project Gutenberg ebook 78050 and Wikisource
Verification status: directly collated against the facsimile and checked
against two independent digital witnesses; the formal audit is recorded in
`reviews/Q208-review.md`. Physical line breaks are editorially reflowed while
the English, punctuation, formula structure and footnote are retained. No
authorial print error or witness divergence requiring `sic`, `corr.`, or
`conj.` was found.
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

/-- Audited scope reading of ✱2·2. -/
def star_2_2_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ⊃ . p ∨ q"
  parsed := p ⊃ₚ (p ∨ₚ q)
  scopeReading := "The single dots delimit p as antecedent and p ∨ q as consequent."

def star_2_2_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "⊢ . Add . ⊃ ⊢ (1); [Perm] (2); [Syll.] ⊢ .(1).(2). ⊃ ⊢ . Prop"

/-- ✱2·2, preserving Add, Perm and the printed Syll. in that order. -/
theorem star_2_2 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (p ∨ₚ q)) := by
  have line1 : ⊢ₚ (p ⊃ₚ (q ∨ₚ p)) := PM.Derivation.star_1_3 q p
  have line2 : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) := PM.Derivation.star_1_4 q p
  have syll := star_2_05 p (q ∨ₚ p) (p ∨ₚ q)
  exact PM.Derivation.detach line1 (PM.Derivation.detach line2 syll)

/-- Audited scope reading of ✱2·21. -/
def star_2_21_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : ∼p . ⊃ . p ⊃ q"
  parsed := ∼ₚ p ⊃ₚ (p ⊃ₚ q)
  scopeReading := "The target is the exact ✱2·2 instance with ∼p in place of p."

def star_2_21_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·2  ∼p/p]"

/-- ✱2·21, exactly the printed substitution instance of ✱2·2. -/
theorem star_2_21 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ p ⊃ₚ (p ⊃ₚ q)) :=
  star_2_2 (∼ₚ p) q

/-- Audited scope reading of ✱2·24. -/
def star_2_24_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ⊃ . ∼p ⊃ q"
  parsed := p ⊃ₚ (∼ₚ p ⊃ₚ q)
  scopeReading := "Comm exchanges the two antecedents in the exact ✱2·21 result."

def star_2_24_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·21.Comm]"

/-- ✱2·24, the printed `✱2·21.Comm` construction. -/
theorem star_2_24 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ (∼ₚ p ⊃ₚ q)) := by
  have comm := star_2_04 (∼ₚ p) p q
  exact PM.Derivation.detach (star_2_21 p q) comm

/-- Audited scope reading of ✱2·25. -/
def star_2_25_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :· p : ∨ : p ∨ q . ⊃ . q"
  parsed := p ∨ₚ ((p ∨ₚ q) ⊃ₚ q)
  scopeReading := "The principal connective is ∨: p ∨ ((p ∨ q) ⊃ q)."

def star_2_25_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "⊢ . ✱2·1 . ⊃ ⊢ : ∼(p ∨ q) . ∨ . (p ∨ q) :; [Assoc.] ⊃ ⊢ : p . ∨ . {∼(p ∨ q) . ∨ . q} : ⊃ ⊢ . Prop"

/-- ✱2·25, preserving the printed ✱2·1 then Assoc construction. -/
theorem star_2_25 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ∨ₚ ((p ∨ₚ q) ⊃ₚ q)) := by
  have line1 : ⊢ₚ (∼ₚ (p ∨ₚ q) ∨ₚ (p ∨ₚ q)) := star_2_1 (p ∨ₚ q)
  have assoc := PM.Derivation.star_1_5 (∼ₚ (p ∨ₚ q)) p q
  exact PM.Derivation.detach line1 assoc

/-- Audited scope reading of ✱2·26. -/
def star_2_26_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :· ∼p : ∨ : p ⊃ q . ⊃ . q"
  parsed := ∼ₚ p ∨ₚ ((p ⊃ₚ q) ⊃ₚ q)
  scopeReading := "This is ✱2·25 with ∼p substituted for p."

def star_2_26_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·25  ∼p/p]"

/-- ✱2·26, exactly the displayed substitution instance of ✱2·25. -/
theorem star_2_26 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (∼ₚ p ∨ₚ ((p ⊃ₚ q) ⊃ₚ q)) :=
  star_2_25 (∼ₚ p) q

/-- Audited scope reading of ✱2·27. -/
def star_2_27_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :· p . ⊃ : p ⊃ q . ⊃ . q"
  parsed := p ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)
  scopeReading := "The outer implication is the ✱1·01 reading of the leading disjunction in ✱2·26."

def star_2_27_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·26]"

/-- ✱2·27, solely the printed ✱1·01 reading of ✱2·26. -/
theorem star_2_27 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ⊃ₚ ((p ⊃ₚ q) ⊃ₚ q)) :=
  star_2_26 p q

/-- Audited scope reading of ✱2·3. -/
def star_2_3_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ (q ∨ r) . ⊃ . p ∨ (r ∨ q)"
  parsed := (p ∨ₚ (q ∨ₚ r)) ⊃ₚ (p ∨ₚ (r ∨ₚ q))
  scopeReading := "The displayed parentheses fix both nested disjunctions; the principal connective is implication."

def star_2_3_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm (q, r)/(p, q)] ⊢ : q ∨ r . ⊃ . r ∨ q :; [Sum (q ∨ r, r ∨ q)/(q, r)] ⊃ ⊢ : p ∨ (q ∨ r) . ⊃ . p ∨ (r ∨ q)"

/-- PM ✱2·3: Perm `q r`, raised by Sum `p`, then detached. -/
theorem star_2_3 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ (p ∨ₚ (r ∨ₚ q))) :=
  PM.Derivation.detach
    (PM.Derivation.star_1_4 q r)
    (PM.Derivation.star_1_6 p (q ∨ₚ r) (r ∨ₚ q))

/-- Audited scope reading of ✱2·31. -/
def star_2_31_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ (q ∨ r) . ⊃ . (p ∨ q) ∨ r"
  parsed := (p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r)
  scopeReading := "The theorem changes right-nesting into the explicitly printed left-nesting."

def star_2_31_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[✱2·3] p ∨ (q ∨ r) ⊃ p ∨ (r ∨ q); [Assoc (r, q)/(q, r)] ⊃ r ∨ (p ∨ q); [Perm (r, p ∨ q)/(p, q)] ⊃ (p ∨ q) ∨ r : ⊃ ⊢ . Prop"

/-- PM ✱2·31, expanding PM's newly stated sorites abbreviation with ✱2·05. -/
theorem star_2_31 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r)) :=
  PM.Derivation.detach
    (PM.Derivation.detach
      (star_2_3 p q r)
      (PM.Derivation.detach
        (PM.Derivation.star_1_5 p r q)
        (star_2_05 (p ∨ₚ (q ∨ₚ r)) (p ∨ₚ (r ∨ₚ q)) (r ∨ₚ (p ∨ₚ q)))))
    (PM.Derivation.detach
      (PM.Derivation.star_1_4 r (p ∨ₚ q))
      (star_2_05 (p ∨ₚ (q ∨ₚ r)) (r ∨ₚ (p ∨ₚ q)) ((p ∨ₚ q) ∨ₚ r)))

/-- Audited scope reading of ✱2·32. -/
def star_2_32_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : (p ∨ q) ∨ r . ⊃ . p ∨ (q ∨ r)"
  parsed := ((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))
  scopeReading := "This is the converse associative direction, with both bracketings explicit."

def star_2_32_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm (p ∨ q, r)/(p, q)] (p ∨ q) ∨ r ⊃ r ∨ (p ∨ q); [Assoc (r, p, q)/(p, q, r)] ⊃ p ∨ (r ∨ q); [✱2·3] ⊃ p ∨ (q ∨ r) : ⊃ ⊢ . Prop"

/-- PM ✱2·32, expanding the same sorites abbreviation in printed order. -/
theorem star_2_32 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))) :=
  PM.Derivation.detach
    (PM.Derivation.detach
      (PM.Derivation.star_1_4 (p ∨ₚ q) r)
      (PM.Derivation.detach
        (PM.Derivation.star_1_5 r p q)
        (star_2_05 ((p ∨ₚ q) ∨ₚ r) (r ∨ₚ (p ∨ₚ q)) (p ∨ₚ (r ∨ₚ q)))))
    (PM.Derivation.detach
      (star_2_3 p r q)
      (star_2_05 ((p ∨ₚ q) ∨ₚ r) (p ∨ₚ (r ∨ₚ q)) (p ∨ₚ (q ∨ₚ r))))

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

/- PM-VERBATIM-BEGIN PM1:✱2·36
✱2·36.  ⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . r ∨ p

Dem.

        [Perm]  ⊢ : p ∨ r . ⊃ . r ∨ p :
        [Syll  (p ∨ q, p ∨ r, r ∨ p)/(p, q, r)]
                ⊃ ⊢ :. p ∨ q . ⊃ . p ∨ r : ⊃ :
                         p ∨ q . ⊃ . r ∨ p                    (1)
        [Sum]   ⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r  (2)
        ⊢ .(1).(2).Syll. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱2·36 -/

/- PM-FORMAL-GLOSS
The four printed stages are preserved: Perm, the displayed specialized Syll.,
Sum, then the final Syll.  Both syllogisms are expanded only through ✱2·05
and metalinguistic detachment.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·37
✱2·37.  ⊢ :. q ⊃ r . ⊃ : q ∨ p . ⊃ . p ∨ r
                                            [Syll.Perm.Sum]
PM-VERBATIM-END PM1:✱2·37 -/

/- PM-VERBATIM-BEGIN PM1:✱2·38
✱2·38.  ⊢ :. q ⊃ r . ⊃ : q ∨ p . ⊃ . r ∨ p
                                            [Syll.Perm.Sum]

The proofs of ✱2·37·38 are exactly analogous to that of ✱2·36. (We use
"✱2·37·38" as an abbreviation for "✱2·37 and ✱2·38." Such abbreviations
will be used throughout.)

The use of a general principle of deduction, such as either form of "Syll,"
in a proof, is different from the use of the particular premisses to which
the principle of deduction is applied. The principle of deduction gives the
general rule according to which the inference is made, but is not itself a
premiss in the inference. If we treated it as a premiss, we should need either
it or some other general rule to enable us to infer the desired conclusion,
and thus we should gradually acquire an increasing accumulation of premisses
without ever being able to make any inference. Thus when a general rule is
adduced in drawing an inference, as when we write
"[Syll] ⊢ .(1).(2). ⊃ ⊢ . Prop," the mention of "Syll" is only required in
order to remind the reader how the inference is drawn.

The rule of inference may, however, also occur as one of the ordinary
premisses, that is to say, in the case of "Syll" for example, the proposition
"p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r" may be one of those to which our rules
of deduction are applied, and it is then an ordinary premiss. The distinction
between the two uses of principles of deduction is of some philosophical
importance, and in the above proofs we have indicated it by putting the rule
of inference in square brackets. It is, however, practically inconvenient to
continue to distinguish in the manner of the reference. We shall therefore
henceforth both adduce ordinary premisses in square brackets where convenient,
and adduce rules of inference, along with other propositions, in asserted
premisses, i.e. we shall write e.g.

        "⊢ .(1).(2).Syll. ⊃ ⊢ . Prop"
        rather than     "Syll ⊢ .(1).(2). ⊃ ⊢ . Prop"
PM-VERBATIM-END PM1:✱2·38 -/

/- PM-FORMAL-GLOSS
PM says that ✱2·37 and ✱2·38 are exactly analogous to ✱2·36. Their Lean
terms therefore expose the input and output Perm instances and expand each
printed Syll. through the two previously proved forms ✱2·05 and ✱2·06.
-/

/- PM-VERBATIM-BEGIN PM1:✱2·41
✱2·41.  ⊢ :. q . ∨ . p ∨ q : ⊃ . p ∨ q

Dem.

        [Assoc  (q, p, q)/(p, q, r)]
              ⊢ :. q . ∨ . p ∨ q : ⊃ : p . ∨ . q ∨ q :
        [Taut.Sum]  ⊃ : p ∨ q : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱2·41 -/

/- PM-FORMAL-GLOSS
The proof keeps the printed `Assoc q p q` instance, followed by Taut at `q`
lifted with Sum at `p`, and the concluding Syll. composition.
-/

/- PM-EDITORIAL
Source for ✱2·36–✱2·38 and ✱2·41:
- scan, printed pp. 110–111: https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/132 and /133
- working witnesses: Project Gutenberg ebook 78050 and Wikisource
Verification status: double-witness-checked and collated directly against the
facsimile; the source and formal audit is recorded in `reviews/Q209-review.md`.
Project Gutenberg's `data-tex` corrupts two expressions in the demonstration
of ✱2·36 (`p ∨ r` and `q ⊃ r`); the readings above follow the scan. These are
digital-witness errors, not errors in the 1910 impression, so no `[sic]`,
`corr.`, or `conj.` entry is attached.
-/

/-! ## Q209: audited scope readings and formal derivations -/

def star_2_36_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : p ∨ q . ⊃ . r ∨ p"
  parsed := (q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ p))
  scopeReading := "The outer antecedent is q ⊃ r; its consequent is (p ∨ q) ⊃ (r ∨ p)."

def star_2_36_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Perm]; [Syll (p ∨ q, p ∨ r, r ∨ p)/(p, q, r)] (1); [Sum] (2); [(1).(2).Syll.] ⊢ .Prop"

theorem star_2_36 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ p))) := by
  have perm : ⊢ₚ ((p ∨ₚ r) ⊃ₚ (r ∨ₚ p)) := PM.Derivation.star_1_4 p r
  have syll : ⊢ₚ (((p ∨ₚ r) ⊃ₚ (r ∨ₚ p)) ⊃ₚ
      (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ p)))) :=
    star_2_05 (p ∨ₚ q) (p ∨ₚ r) (r ∨ₚ p)
  have line1 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ p))) :=
    PM.Derivation.detach perm syll
  have line2 : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.star_1_6 p q r
  exact PM.Derivation.detach line2
    (PM.Derivation.detach line1
      (star_2_05 (q ⊃ₚ r) ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((p ∨ₚ q) ⊃ₚ (r ∨ₚ p))))

def star_2_37_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : q ∨ p . ⊃ . p ∨ r"
  parsed := (q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))
  scopeReading := "The outer antecedent is q ⊃ r; its consequent is (q ∨ p) ⊃ (p ∨ r)."

def star_2_37_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Syll.Perm.Sum]"

theorem star_2_37 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))) := by
  have permIn : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) := PM.Derivation.star_1_4 q p
  have syll : ⊢ₚ (((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) ⊃ₚ
      (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r)))) :=
    star_2_06 (q ∨ₚ p) (p ∨ₚ q) (p ∨ₚ r)
  have line1 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach permIn syll
  have sum : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) := PM.Derivation.star_1_6 p q r
  exact PM.Derivation.detach sum
    (PM.Derivation.detach line1
      (star_2_05 (q ⊃ₚ r) ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))))

def star_2_38_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q ⊃ r . ⊃ : q ∨ p . ⊃ . r ∨ p"
  parsed := (q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))
  scopeReading := "The outer antecedent is q ⊃ r; its consequent is (q ∨ p) ⊃ (r ∨ p)."

def star_2_38_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Syll.Perm.Sum]"

theorem star_2_38 {Γ : PM.RealContext} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) := by
  have permIn : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) := PM.Derivation.star_1_4 q p
  have permOut : ⊢ₚ ((p ∨ₚ r) ⊃ₚ (r ∨ₚ p)) := PM.Derivation.star_1_4 p r
  have line1 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r))) :=
    PM.Derivation.detach permIn (star_2_06 (q ∨ₚ p) (p ∨ₚ q) (p ∨ₚ r))
  have line2 : ⊢ₚ (((q ∨ₚ p) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) :=
    PM.Derivation.detach permOut (star_2_05 (q ∨ₚ p) (p ∨ₚ r) (r ∨ₚ p))
  have line3 : ⊢ₚ (((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ⊃ₚ ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))) :=
    PM.Derivation.detach line2
      (PM.Derivation.detach line1
        (star_2_06 ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))))
  have sum : ⊢ₚ ((q ⊃ₚ r) ⊃ₚ ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r))) := PM.Derivation.star_1_6 p q r
  exact PM.Derivation.detach sum
    (PM.Derivation.detach line3
      (star_2_05 (q ⊃ₚ r) ((p ∨ₚ q) ⊃ₚ (p ∨ₚ r)) ((q ∨ₚ p) ⊃ₚ (r ∨ₚ p))))

def star_2_41_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. q . ∨ . p ∨ q : ⊃ . p ∨ q"
  parsed := (q ∨ₚ (p ∨ₚ q)) ⊃ₚ (p ∨ₚ q)
  scopeReading := "The dots override ✱2·33: the antecedent is q ∨ (p ∨ q)."

def star_2_41_demonstration_printed : PM.PrintedFormula :=
  PM.pmPrinted "[Assoc (q, p, q)/(p, q, r)]; [Taut.Sum] ⊃ ⊢ .Prop"

theorem star_2_41 {Γ : PM.RealContext} (p q : PM.Elementary Γ) :
    ⊢ₚ ((q ∨ₚ (p ∨ₚ q)) ⊃ₚ (p ∨ₚ q)) := by
  have assoc : ⊢ₚ ((q ∨ₚ (p ∨ₚ q)) ⊃ₚ (p ∨ₚ (q ∨ₚ q))) := PM.Derivation.star_1_5 q p q
  have taut : ⊢ₚ ((q ∨ₚ q) ⊃ₚ q) := PM.Derivation.star_1_2 q
  have line2 : ⊢ₚ ((p ∨ₚ (q ∨ₚ q)) ⊃ₚ (p ∨ₚ q)) :=
    PM.Derivation.detach taut (PM.Derivation.star_1_6 p (q ∨ₚ q) q)
  exact PM.Derivation.detach assoc
    (PM.Derivation.detach line2
      (star_2_05 (q ∨ₚ (p ∨ₚ q)) (p ∨ₚ (q ∨ₚ q)) (p ∨ₚ q)))

end PM.FirstEdition.Volume1.Star2
