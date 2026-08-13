# Q226 strict reconstruction continuation — reject unlicensed primitives

The preceding terminal archive is rejected.  Although it compiles, it used
unlicensed primitive propositions ✱1·5 and ✱1·6 in targets ✱3·45, ✱3·47,
and ✱3·48, and added the undefined `syllRuleQ220` scaffolding.  Neither a
primitive constructor nor an item present merely in the isolated context is a
proof permission.

Reconstruct the four original declarations, in order and with their exact
Q226 statements, using only the exact per-target whitelists and explicitly
licensed inference conventions in `aristotle/manifests/Q226.json`.  Preserve
the scanned ASTs and printed substitutions.  In particular, do not use
`PM.Derivation.star_1_5`, `PM.Derivation.star_1_6`, any other unlisted Star1
constructor, `syllRuleQ220`, a new helper rule, any unlisted Star2/Star3
theorem, `Classical`, axioms, `sorry`, `admit`, `unsafe`, or a semantic
shortcut.

Every printed citation and every permitted detachment must appear explicitly
in a per-target ledger.  If a target is impossible under its exact whitelist,
leave it unproved and provide a machine-checkable obstruction which identifies
the precise missing printed citation/inference.  Do not silently relax any
policy.  Return a self-contained compiling Lean file and the ledger.
