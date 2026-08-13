# Q300 kernel-link remediation

The previous archive is rejected. Its proof recreated a local `PM` system,
used `Classical` in `Main.lean`, and did not provide an exact declaration
matching `PM.Architecture.FirstOrderPrerequisites.star_9_21`.

Return only the target body for the exact Q300 interface target, importing or
referring only to the real declarations exposed by the supplied context bundle.
Do not define `PM`, syntax, deduction, semantics, helpers, or local copies of
any prerequisite. Do not use `Classical`, `axiom`, `sorry`, `admit`, `unsafe`,
or a target primitive. If the context does not expose an exact real kernel
constant required by the printed proof, stop and state that missing declaration
and its required signature explicitly; do not emulate it locally.
