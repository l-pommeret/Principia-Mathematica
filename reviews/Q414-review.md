# Q414 strict semantic review — PM II ✱102·36, ·361, ·37

✱102·36 and ·361 pass under PM's contextual-description reading of `E!` as
asserting that the displayed incomplete symbol has a value. For each typed
argument `b`, `star_102_36` exhibits the class value `Nc b`; `star_102_361`
packages the same determination as an inhabited subtype of values equal to
`Nc b`. Equality to the fixed fibre makes the value unique extensionally, so
neither reconstruction drops the determinacy carried by the notation. Both
items are promoted to `awaiting-ci`. Their Lean proofs are constructor-level
and have empty direct theorem graphs; the printed citations remain preserved.

✱102·37 is refused. PM asserts the class equality between the converse domain
of the assigned `Nc` relation and the universal beta-type class. Lean's
`star_102_37` proves only `∃ μ, μ = Nc b` for a single already typed argument
by invoking `star_102_36`. It exposes no converse-domain class and proves
neither inclusion of the printed equality. Its actual direct Lean dependency
is ✱102·36. The refusal is isolated in
`PM2-star-102-Q414-refused.json`, with no duplicate item in the accepted lot.
