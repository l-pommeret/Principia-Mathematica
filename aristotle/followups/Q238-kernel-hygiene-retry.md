# Q238 kernel hygiene retry

Operational retry only; `retry_of` remains canonical Q238.  Deliver only
`star_4_7`, `star_4_71`, and `star_4_72` against the reviewed interface and
its printed whitelist.  Do not supply Star1/Star2/Star3 modules, copies of
dependencies, helpers, imports, definitions, or a local namespace.  `Classical`
is permitted only in the generated `Main.lean` compilation harness, never in a
target or dependency file.  `axiom`, `sorry`, `admit`, and `unsafe` are banned.
Return the exact obstruction instead of changing context or permissions.
