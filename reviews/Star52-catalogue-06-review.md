# PM I ✱52 catalogue-06 strict semantic audit

All five items ·44, ·45, ·46, ·6 and ·601 are exact typed contextual
translations.  The first three preserve the displayed equivalences for
singleton intersections, inclusions and unions.  The last two retain the
unique-member interpretation of the incomplete description: no arbitrary
default value is chosen, and both universal and existential predicate forms
are present.  All five are marked `awaiting-ci`.

Direct parser testing rejects only ·45 and ·46 because the incomplete-symbol
context is not explicit enough for the deterministic grammar.  Their existing
`reviewed-gap` classifications remain justified; ·44, ·6 and ·601 parse and
are left without parser overrides.
