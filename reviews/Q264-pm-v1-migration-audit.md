# Q264 strict PM-v1 migration audit

Scope: ✱10·01, ·02, ·03, ·1, and ·11. The mandatory comparison point is
`Principia/FirstEdition/Volume1/Part1/SectionA/Star2.lean`; the axiom report is
`/tmp/pm-axioms-report.txt`.

The nine migration tests are: **T1** literal source; **T2** indexed PM syntax;
**T3** assertion represented by a judgement, not a formula node; **T4** `Df`
only unfolded; **T5** kernel-checked PM proof payload; **T6** explicit real
numbered calls; **T7** separate printed and implementation graphs; **T8** no
`Support`, Raw-to-assertion escape, or empty proof constructor; **T9** public
declaration reported axiom-free.

✱10·01–·03 pass as definitions, not derivations. They construct the assigned
`FirstOrder` AST and unfold exactly the printed existential, formal implication,
and formal equivalence definiens. Their graphs are empty, hence their level is
`pm-definition-v1`, never `pm-derivation-v1`.

✱10·1 passes as a complete narrow PM derivation. Its exact mixed `Raw` endpoint
is `(x).φx ⊃ φy`; `Star92KernelAssertion` requires the real ✱2·1
`PM.Derivation`, the ordered ✱9·1 instance, and explicit ✱9·05/·01
normalizations through that endpoint. Q264 calls `Star92Kernel.derive`; its
implementation-reuse edge normalizes to ✱9·2 and is not a printed citation.

✱10·11 concludes an actual `OrderedAssertion (always φ)` from the asserted
open matrix and directly calls `OrderedAssertion.star_9_13`. Its reuse edge to
✱9·13 is explicit; the primitive source prints no predecessor.

The report marks all five declarations axiom-free, and neither implementation
module contains `Support`. No semantic `Prop` theorem substitutes for the PM
judgements. Verdict: three `pm-definition-v1` items and two
`pm-derivation-v1` items remain kernel-checked.

