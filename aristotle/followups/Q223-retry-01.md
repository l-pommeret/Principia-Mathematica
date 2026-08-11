# Q223 fidelity continuation

The terminal archive compiles but is rejected under the exact manifest: its
`star_3_27` and `star_3_31` call `PM.Derivation.star_1_6`, which is context
scaffolding and not in either target's whitelist. Reuse only conforming work.

Repair `star_3_27` and `star_3_31` using exclusively their exact listed
declarations and earlier local targets licensed in `aristotle/Q223.md` /
`aristotle/manifests/Q223.json`. Do not use `star_1_6`, Syll, or any unlisted
reference. Preserve the exact target statements. The printed terminal `Prop`
is not a permission for a primitive inference rule: under this policy it may
be represented only by the reviewed detachment convention when explicitly
licensed; neither target currently licenses it, so avoid it too.

No axioms, Classical, semantics, sorry/admit/unsafe, helper theorems, or
target weakening. Return complete proof terms whose actual dependencies are
visible to the audit.
