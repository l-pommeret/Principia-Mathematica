# ✱32 catalogue 03 strict semantic audit

The five literal source blocks PM1:✱32·133, ·14, ·15, ·18, and ·181 match their catalogue records and were compared individually with the named declarations in `Star32ConsecutiveKernel.lean` and `Star32ConsecutiveKernel2.lean`.

All five translations pass strict typed equivalence. For ·133, the typed reading of `B ←R x` is equality with the left section, and `leftSection R x` unfolds to the printed class abstract `fun y => R x y`. Propositions ·14 and ·15 state exactly the injectivity of the full right- and left-section maps, respectively; function extensionality proves the converse relation equality without strengthening the statement. Finally, class membership in a right or left section is function application in the typed reconstruction, so ·18 and ·181 reduce exactly to `R x y`.

No item is refused. The accepted proof bodies use only local sectional definitions, equality elimination, function extensionality, and private local helpers; they contain no direct numbered-proposition references. The recorded historical/Lean dependency graphs therefore remain empty for these declarations under the existing catalogue policy. All five records are promoted in place to `awaiting-ci`; CI evidence remains pending.
