# ✱9·31 canonical scope audit

Source: first edition volume I, printed p. 140, scan leaf 162.  Canonical
transcription: `Principia/FirstEdition/Volume1/Star9.lean`; independent local
collation: `aristotle/demonstrations/PM1-star-9-31.txt`.

The five displayed proof lines are:

1. `(y) : φx ∨ φy ⊃ (∃z).φz`, from ✱9·11 and the first ✱9·13;
2. `(∃y).(φx ∨ φy) ⊃ (∃z).φz`, by ✱9·03·02;
3. `(x) : ((∃y).(φx ∨ φy) ⊃ (∃z).φz)`, by the second ✱9·13;
4. `(∃x)(∃y).(φx ∨ φy) ⊃ (∃z).φz`, by ✱9·03·02;
5. `((∃x).φx ∨ (∃y).φy) ⊃ (∃z).φz`, by ✱9·05·06.

Binder names are expository only, but their relative scopes are not.  In
particular line 3 universally closes the whole line-2 implication.  It must
not be encoded by universally wrapping a Raw term that has already pushed
the line-2 quantifiers through that implication.  Lines 3 and 4 therefore
require explicit non-smart redex ASTs before any `NormalizesScoped`
certificate is constructed.

The canonical implementation must keep the following distinctions:

- `smartDisjScoped` is permitted for the normalized line-2 matrix carrier;
- the displayed line-3 and line-4 redexes must use explicit `.neg`, `.disj`,
  and `.quantified` nodes;
- ✱9·03·02 and ✱9·05·06 are syntax-normalization certificates, not new
  `OrderedAssertion` constructors;
- the final target is the existing `FirstOrderQ259.star_9_31_target`.

Current integration status: the line-2 scoped carrier and its second-✱9·13
carrier are kernel-checked.  The remaining gate is an exact canonical
embedding of the unnormalized line-3 carrier; using the already-normalized
`line2ScopedRaw` as its body would collapse a printed proof step and is not
accepted by this audit.
