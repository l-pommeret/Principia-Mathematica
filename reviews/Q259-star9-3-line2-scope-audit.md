# Scope audit — PM I, ✱9·3, demonstration line (2)

Verdict: **the existential `(∃y)` scopes the entire implication**
`φx ∨ φy ⊃ φx`, not merely its antecedent.

The canonical 1910 facsimile is printed p. 139, scan leaf 161 (the Q259 item
is on the following printed p. 140 / leaf 162). In the displayed demonstration
the line is set as `(∃y): φx ∨ φy . ⊃ . φx`; the colon immediately after
the binder has the wider PM dot scope. The proof’s next line repeats this
scope as `(x): (∃y): φx ∨ φy . ⊃ . φx`. The independent Project Gutenberg
78050 transcription has the same colon/dot placement. The Wikisource control
witness for leaf 161 likewise prints line (2) with `(∃y):φx ∨ φy . ⊃ . φx`.

Consequently the correct normalized matrix is `sometimes (matrixImp
(φx ∨ φy) φx)`. It is **not** `impFirstToMatrix (sometimes (φx ∨ φy)) φx`.
The existing `star_9_3_line2_target` must be corrected before it can serve as
the exact source target. This audit changes no derivation claim.

Witnesses consulted: PM1-1910-SCAN leaf 161 / printed p. 139; PG78050;
Wikisource `Page:Russell, Whitehead - Principia Mathematica, vol. I,
1910.djvu/161`.
