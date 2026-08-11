# Q230 continuation — unconditional kernel-linked targets only

The immediately preceding terminal archive (task
`10a8091f-5cbd-432b-b02b-cef2eb5f5ee1`, immutable SHA-256
`5262e7997815a50ef0103976f981c97cae89e522b013d14c2141a9785c76e527`)
is not an acceptable completion.  Its four declarations add named hypotheses
for missing rules, so it proves conditional variants rather than the exact
unconditional targets.  It also packages archive-local `Context.lean` and
`Star4Interface.lean`; those are not accepted kernel dependencies and cannot
be copied or remapped into a solution.

Continue this same project.  The only acceptable Lean deliverable is exactly,
and in order, the unconditional declarations from `Q230.md`:
`star_4_3`, `star_4_31`, `star_4_32`, and `star_4_33`, with precisely their
submitted signatures.  Preserve the editorial notes, including the general
φ-symmetry note for ✱4·3 and the tacit ✱4·22 note for ✱4·32.

Use a declaration only when it is already an accepted, project-visible kernel
body and it is on that target's exact whitelist.  In particular, do not add a
parameter/hypothesis for any missing rule or theorem; do not import, recreate,
transcribe, remap, or depend on a local context/interface/module/archive; and
do not use `Classical`, `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`,
or helpers (including `equiv`, `equivChain`, `equivIntro`, `equivImp`, `adj`).
Do not redefine or unfold ✱4·01, and do not widen/narrow a target.

First inspect the current project's declarations.  If accepted kernel bodies
for every required whitelisted item are visible, replace the conditional
surrogates with direct proofs and verify no local-copy/remap artifact remains.
If any is not visible, make no substitute Lean declarations and return a short
per-target report naming the exact missing kernel declaration(s) and why each
is required.  That report is evidence of an obstruction, not a completion.
