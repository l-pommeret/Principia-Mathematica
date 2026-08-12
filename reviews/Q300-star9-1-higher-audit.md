# Audit Q300 — closed higher instance of PM I ✱9·1

## Source basis

- First edition, volume I, printed pp. 138–139; canonical scan leaf 161
  (Commons derivative SHA-256 recorded in `Q300-review.md`).
- Diplomatic proof: `aristotle/demonstrations/PM1-star-9-21.txt`, lines (2)
  and (3).
- Primitive source text: `Principia/FirstEdition/Volume1/Star9.lean`, ✱9·1:
  `⊢:φx.⊃.(∃z).φz  Pp`; its statement does not restrict `φ` to an
  elementary matrix.

## Exact instantiated shape

For the second application in ✱9·21, let
`χ(x) := (∃y): (φx ⊃ ψx) ⊃ (φy ⊃ ψz)`.
Line (2) is the displayed value `χ(z)`, and line (3) is its existential
closure `(∃x):χ(x)`.  The target is therefore exactly
`FirstOrderMatrix.star_9_1_higher_target χ z`: its reduction is
`(∃x): ∼χ(z) ∨ χ(x)`, with `χ(z)` explicitly weakened below the new binder.

## Boundary

This audit licenses only that one syntactic target shape for the printed
second occurrence of ✱9·1.  It does **not** license an order-polymorphic
Pp, a general promotion/coercion between assigned orders, or an assertion
constructor before the target has a matching `OrderedFormula` carrier and a
typed detachment path from line (2).
