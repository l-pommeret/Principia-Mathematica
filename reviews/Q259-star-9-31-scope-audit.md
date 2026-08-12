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
- the initially proposed final target was
  `FirstOrderQ259.star_9_31_target`; the correction below supersedes it.

## Assigned-order correction

That last identification was rejected by local Lean checking.  The second
application of ✱9·13 retains an assigned-order universal carrier, so the
source-faithful endpoint begins with an outer `always`; the historical
`FirstOrderQ259.star_9_31_target` is an order-one formula and omits it.
Moreover, replacing the two displayed occurrences by the original apparent
matrix is not alpha/beta conversion when that matrix contains its bound
argument.  `Star931Kernel.exactTargetRaw` therefore records the literal
closed endpoint produced by the scan's line (3), ✱9·03·02 and ✱9·05·06.
The old order-one target remains available for compatibility but is not used
as the endpoint certificate for the canonical proof.

Final integration status: `Q259ClosedRuleBook.star_9_31` exposes exactly
`Nonempty (Star931KernelAssertion φ)`.  Its literal line-3 carrier, the
✱9·03·02 and ✱9·05·06 certificates, and the source-faithful Raw endpoint were
kernel-checked at immutable commit
`eda99d1ed844362805f3f05805d4fc8e72e7c4a9` by GitHub Actions run
`31572372279` (`success`).  This evidence does not claim an `OrderedAssertion`.
