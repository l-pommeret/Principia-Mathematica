# Q296 retry-02 — exact canonical rfl target

Return exactly the live declaration
`PM.DescriptionSyntax.Formula.star_14_01` with the supplied signature and
body `rfl`. The archive must contain no file, text, comment, import, copied
context, helper, theorem, definition, namespace wrapper beyond the supplied
target, or local declaration mentioning `expand_descriptionScope`.

`Classical` is forbidden anywhere in the archive, including `Main.lean` and
comments. So are `axiom`, `opaque`, `sorry`, `admit`, `unsafe`, imports and
all local syntax/model scaffolding. If the supplied interface does not make
the exact target definitional, return only the named obstruction.
