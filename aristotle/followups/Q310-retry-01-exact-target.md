# Q310 retry-01 — three canonical rfl targets only

Return only the three supplied live canonical declarations
`PM.FirstEdition.Volume1.Star14Source.star_14_02`, `star_14_03`, and
`star_14_04`, with byte-exact supplied signatures and each body exactly `rfl`.
Do not copy `DescriptionContext`, add imports, a `Main.lean` configuration,
namespace/helper/theorem/definition, or any local syntax/context.

`Classical` is forbidden anywhere in the complete archive, including comments
and `Main.lean`. So are `axiom`, `opaque`, `sorry`, `admit`, `unsafe`, and any
non-target declaration. If one supplied target is not definitional in the
interface, return only its named obstruction.
