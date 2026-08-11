# Q241 kernel hygiene retry

Operational continuation of canonical Q241 only.  Deliver exactly
`star_4_82`, `star_4_83`, `star_4_84`, and `star_4_85` at their existing
canonical target types and against the reviewed interface and printed
whitelist.  Reuse only the explicitly supplied kernel constants; do not add
modules, imports, definitions, helpers, local copies of dependencies, or a
local namespace.

`sorry`, `admit`, `axiom`, `unsafe`, `Classical`, native-connective
substitutions, generic rules, and placeholder declarations are forbidden in
every delivered target or dependency file.  `Classical` is allowed only in a
generated `Main.lean` compilation harness.  Preserve the printed expansions
`Imp=✱3·31`, `Simp=✱3·26`, and `Comp=✱3·43` only through proved bodies.  If
the reviewed interface is insufficient, return the exact per-target
obstruction; do not change the target, whitelist, context, or permissions.
