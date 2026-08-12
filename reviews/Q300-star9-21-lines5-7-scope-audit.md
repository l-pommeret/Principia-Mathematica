# Audit Q300 — PM I ✱9·21, lignes (5)–(7)

## Witnesses

- First edition, volume I, printed pp. 138–139, canonical scan leaf 161;
  derivative checksum recorded in `reviews/Q300-review.md`.
- Diplomatic source block: `Principia/FirstEdition/Volume1/Star9.lean`.
- Parsed proof witness: `aristotle/demonstrations/PM1-star-9-21.txt`.

## Collated scope readings

| line | printed transformation | canonical scope reading |
| --- | --- | --- |
| (5) | `(4).(✱9·06)` | The existential `x` remains inside the outer universal `z`; the negated antecedent is moved beneath that existential, while `(∃y).φy⊃ψz` stays on the right of the implication. |
| (6) | `(5).(✱1·01.✱9·08)` | ✱1·01 expands the displayed implication as negation/disjunction. ✱9·08 then gives outer universal `z`, inner existential `y`, with the left existential negation retained as the left disjunct. |
| (7) | `(6).(✱9·08)` | The right-hand universal on `ψz` is moved under the existing existential `y`; no binder is discarded and the left existential negation remains outside that right scope. |

The final ✱1·01 is an implication abbreviation only. The closing sentence
identifies `y`/`z` with the schematic binder name `x` by explicit
capture-avoiding alpha-renaming, not by a semantic equality.

## Diplomatic transcription of the three displayed lines

The page witness renders the relevant tail of the demonstration as follows
(dots and colons retained as scope punctuation):

```text
[(4).(✱9·06)]             ⊢ ::(z)::(∃x):. φx ⊃ ψx .⊃ :(∃y). φy ⊃ ψz     (5)
[(5).(✱1·01.✱9·08)]      ⊢ :.(∃x).∼(φx ⊃ ψx) :∨: (z):(∃y).∼φy ∨ ψz       (6)
[(6).(✱9·08)]            ⊢ :.(∃x).∼(φx ⊃ ψx) :∨: (z):(∃y).∼φy ∨ ψz       (7)
[(7).(✱1·01)]            ⊢ :.(x).φx ⊃ ψx .⊃ :(y).φy .⊃ .(z).ψz
```

This transcription was collated against the first-edition scan leaf 161,
printed p. 139, and the proofread page witness.  In particular, line (6)
has the existential `x` outside the disjunction, while its right disjunct
retains the universal `z` followed by existential `y`; line (7) is printed
with the same visible scope pattern and is the subsequent ✱9·08
normalization before the final implication abbreviation.

## Encoding boundary

The `Raw` target must retain the binder sequence shown above.  It may use the
canonical `smartNeg`/`smartDisj` calculations only after the corresponding
explicit source-labelled target is declared; the normalizer is not evidence
for choosing that target.
