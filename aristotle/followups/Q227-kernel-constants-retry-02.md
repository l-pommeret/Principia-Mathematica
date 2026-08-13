# Q227 continuation — consume reviewed kernel constants only

The preceding delivery is rejected.  It reconstructed local declarations named
`PM.FirstEdition.Volume1.Star3.star_3_2` and `star_3_47`, and therefore
introduced a transitive use of `PM.Derivation.star_1_2` through `star_1_6`.
That is forbidden even though the three Star4 target terms otherwise looked
right.

Work from the already-reviewed Q227 isolated context and its **existing,
kernel-checked** declarations:

- `PM.FirstEdition.Volume1.Star3.star_3_2`
- `PM.FirstEdition.Volume1.Star3.star_3_47`

Do not reproduce, shadow, wrap, redefine, or locally prove either constant.
Do not introduce `PM.Q227Packaging`, any helper declaration, or any local
namespace intended to package their proofs.  The delivered `Q227.lean` must
contain only the two required Star4 definitions (`equiv`, `equivChain`) and
the three required Star4 theorems (`star_4_1`, `star_4_12`, `star_4_13`), in
that order, against the reviewed context.  It must make no direct or
transitive use of `PM.Derivation.star_1_2`, `_1_3`, `_1_4`, `_1_5`, or `_1_6`.

Use precisely these theorem permissions, and no others:

- `star_4_1`: `star_2_16`, `star_2_17`, existing `star_3_2`, and primitive
  inference branches `star_1_1` / `star_1_11` only.
- `star_4_12`: `star_2_03`, `star_2_15`, existing `star_3_2`, existing
  `star_3_47`, and primitive inference branches `star_1_1` / `star_1_11`
  only.
- `star_4_13`: `star_2_12`, `star_2_14`, existing `star_3_2`, and primitive
  inference branches `star_1_1` / `star_1_11` only.

`detach` must be expressed by the allowed closed/nonempty branches above;
there are no other additions.  Do not add `Classical`, `axiom`, `sorry`,
`admit`, `unsafe`, imports, alternate syntax, or a new theorem.  Before the
final response, literally audit `Q227.lean` for the forbidden primitive names
and report the exact constants used by each target proof.
