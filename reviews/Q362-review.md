# Q362 review

PM I pp. 231–232 / leaves 253–254 are canonical; PG 78050 agrees. No apparatus or `[sic]` is required.

## Star2/T1–T9 object-judgment audit

The five namesake theorems prove the intended interpreted class-theoretic
propositions, but only at the secondary `Prop` layer. Unlike Star2 and T1–T9,
the module has no object-language formula, judgment identifying the printed
assertion, or `PM.Derivation` term reconstructing the inference. All five
therefore stay `prepared`, blocked on the missing PM derivation/judgment layer;
the ordinary theorem names are recorded only as `statement_declaration`.

The module is axiom-free (`axiom`, `sorry`, `admit`, and unsafe escape hatches
are absent), but axiom-freedom is necessary rather than sufficient. Class
definitions and their `Df` readings are not constructors of `PM.Derivation`.

None of the printed items carries a bracketed citation. Fresh inspection finds
one PM-style Lean call: the secondary proof of ✱24·13 invokes `star_24_12`.
Its graph records that extra reviewed edge; the other four bodies contain no
PM theorem call. No dependency is inherited from the batch or neighbours.

Rebuilt from zero, the printed graphs are empty for all five items. The actual
secondary Lean graphs are respectively `[]`, `[star_24_12]`, `[]`, `[]`, `[]`;
their normalized graphs are `[]`, `[PM1:✱24·12]`, `[]`, `[]`, `[]`.
They document only Prop semantics and cannot substitute for historical PM
derivations.
