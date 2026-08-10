# Proof workflow

Work proceeds in small dependency-closed batches of at most five items.

1. Capture canonical English text and formulae with page-level provenance.
2. Have a dedicated sub-agent check transcription, scope, and dependencies.
3. Encode PM syntax and formulate the exact Lean target.
4. Audit the target before Aristotle submission.
5. Submit only the audited batch; never duplicate an active remote task.
6. Download terminal results immutably and audit them independently.
7. Reject placeholders, new axioms, unsafe escape hatches, weakened targets,
   and omitted cases.
8. Type-check locally at the pinned Lean revision and record immutable CI.

Incomplete Aristotle work continues in the same project. Compiled helper lemmas
do not make an incomplete canonical theorem complete.

