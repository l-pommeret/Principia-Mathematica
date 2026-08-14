# ✱43 catalogue 02 strict semantic audit

The five literal source records PM1:✱43·111, ·112, ·12, ·121, and ·122
were checked against the first-edition witness on printed page 341 and against
their declarations in `Star43OpeningKernel.lean`. Project Gutenberg also
groups these statements among the immediate consequences of the definitions,
with proofs omitted.

No item passes strict source↔Lean equivalence. Proposition ·111 is represented
only by the reflexive equality `product Q R = product Q R`, and ·112 only by
the reflexive equality `product (product R Q) S = product (product R Q) S`.
Those targets erase the printed application of the descriptive functions
`(| R)` and `(R ∥ S)` respectively. They therefore repeat the already-audited
reflexive-target defect of ✱43·11 rather than establish the displayed PM claims.

Propositions ·12, ·121, and ·122 do retain an existence-and-uniqueness shape,
but `uniqueValue` is discharged solely from the local definitions
`leftProduct`, `rightProduct`, and `sandwich`, each defined as equality with
the local `product`. The repository currently has no theorem connecting those
relations and that constructor to PM's incomplete-symbol/descriptive-function
semantics. This is the same source-semantic bridge whose absence blocks
✱43·01, ·1, ·101, and ·102, so these three downstream statements cannot be
promoted independently.

The printed text supplies no numbered proof citations for these five immediate
consequences, and the Lean proof bodies cite no numbered `star_*` declaration.
Consequently both item-level dependency graphs remain empty and agree after
normalization. All five records remain `prepared`, with explicit refusal
statuses; none is marked `awaiting-ci`.
