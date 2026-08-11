# Audit Q222 — association in ✱2·33, ✱3·12, and ✱3·2

Verdict: **the present ASTs are diplomatically correct; Q222 is not eligible
as a strict printed-dependency batch.**  No source defect is established.

## Witnesses examined

- The first-edition scan, p. 110 / leaf 132, prints ✱2·33 as
  `p ∨ q ∨ r .=. (p ∨ q) ∨ r Df` and immediately says that the definition
  serves only to avoid brackets.  It is a convention for a *bare* triple sum,
  not an object-language associativity proposition.
- The first-edition scan, p. 116 / leaf 138, prints both marked connectives in
  ✱3·12: `⊢ : ∼p . ∨ . ∼q . ∨ . p . q`, followed by the sole direct citation
  `[✱2·11 (∼p ∨ ∼q)/p]`.
- The same leaf prints ✱3·2 as `⊢ : p . ⊃ : q . ⊃ . p . q [✱3·12]`.

The checked transcription agrees with the facsimile at all three loci.

## Exact readings

The PM scope marks in ✱3·12 yield

```
((∼p ∨ ∼q) ∨ (p . q)).
```

The marks in ✱3·2 yield the right-nested implication

```
p ⊃ (q ⊃ (p . q)),
```

which expands by ✱1·01 to

```
∼p ∨ (∼q ∨ (p . q)).
```

These are distinct abstract syntax trees.  ✱2·33 cannot change the result:
neither expression is an unmarked `p ∨ q ∨ r` chain, and its text explicitly
limits itself to bracket avoidance.  The existing parser's left-associated
reading of the equal marked sums in ✱3·12 and its right-associated implication
reading in ✱3·2 are therefore both required by the printed scope marks.

## Consequence for the direct citation

The direct citation `[✱3·12]` is genuine but omits the required reassociation
from `((∼p ∨ ∼q) ∨ (p . q))` to `∼p ∨ (∼q ∨ (p . q))`.  The already proved
✱2·32 is exactly that implication direction, with both bracketings explicit.
Using it would be a documented relaxed closure beyond the one printed citation,
not a strict reconstruction.  It must not be silently added to Q222's
whitelist or treated as a consequence of ✱2·33.

The same batch therefore cannot be submitted under the current strict policy.
Any later reconstruction must be separately approved and labelled
`relaxed-associativity-gap`, analogously to Q220; the current audit neither
changes the Q222 AST nor authorizes a proof body or an Aristotle retry.

Sources: [leaf 132 / p. 110](https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/132),
[leaf 138 / p. 116](https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/138).
