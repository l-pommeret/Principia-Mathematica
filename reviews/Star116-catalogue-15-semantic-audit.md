# ✱116 catalogue 15 strict semantic audit

The five loci in catalogue 15 (·5, ·51, ·52, ·529, and ·53) were audited
source-to-Lean against the recorded first-edition statements on printed pages
157–158 (scan leaves 197–198). This audit promotes only claims whose complete
recorded statement is represented by the Lean declaration; compilation alone
is not treated as semantic evidence.

Proposition ·51 is exact in the typed reconstruction. PM's exponential class
becomes the function type, cardinal sum becomes the disjoint sum, and
similarity becomes an explicit equivalence. `sumExpEquiv` gives both maps and
both inverse laws, so no mathematical hypothesis or direction is omitted.
Proposition ·52 is the exact cardinal-class lift of that same equivalence via
·51 and the extensional invariance theorem ·361. These two items are therefore
marked `awaiting-ci`, never prematurely `kernel-checked`.

The other three items are refused. The catalogue entries for ·5 and ·53 retain
only prose summaries in place of PM's displayed constructions and hypotheses;
although their Lean equivalences are mathematically relevant, the available
record cannot establish strict statement equivalence. Item ·529 is a direct
semantic mismatch: PM defines the relation operation `R†` as a restriction of
`R` to its converse, while Lean's `star_116_529` merely reverses a type
equivalence to obtain similarity. All three remain `prepared` with
`blocked-semantic-mismatch` and explicit refusal reasons.

The dependency graphs are kept distinct. The printed ·51 result follows the
construction at ·5, and ·52 follows ·51. Lean ·51 is an alias of `star_116_5`;
Lean ·52 uses ·51 together with the cardinal-class invariance theorem ·361.
The resulting normalized graph records ·5 → ·51 → ·52 plus the additional
Lean closure edge ·361 → ·52. Parser coverage remains `reviewed-gap` because
the historical exponential, similarity, and cardinal arithmetic notation is
not accepted deterministically.

This additional ·361 edge is recorded as a reviewed relaxed closure: it is the
typed extensional passage from similarity to equality of cardinal classes,
not a further printed citation.
