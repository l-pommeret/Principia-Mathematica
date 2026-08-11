# Q229 kernel-link continuation — exact bodies only

The previous archive redefined equivalence and rebuilt `adjoin` from primitive
Star1 rules.  That output is non-linkable.  Work only in the reviewed kernel
context and deliver the four requested target bodies, with no helper or local
module.

- `star_4_21`: `Star3.star_3_22` only.
- `star_4_22`: `Star2.star_2_83`, `Star3.star_3_26`, `Star3.star_3_27`,
  `Star3.star_3_43` only.
- `star_4_24`: `Star2.star_2_43`, `Star3.star_3_2`, `Star3.star_3_26` only.
- `star_4_25`: `Star1.star_1_2`, `Star1.star_1_3` only.

Do not redefine `equiv` or `equivChain`; do not use `adjoin`, any direct
`PM.Derivation.star_1_*`, `detach`, local Principia files, imports, `Classical`,
`axiom`, `sorry`, `admit`, `unsafe`, or any extra theorem.  If a target needs
an unlisted assembly/inference step, report that exact obstruction instead of
constructing it locally.
