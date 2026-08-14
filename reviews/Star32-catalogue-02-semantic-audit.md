# ✱32 catalogue 02 strict semantic audit

The five literal source blocks PM1:✱32·11, ·111, ·12, ·121, and ·132 match their catalogue records and were compared individually with the declarations in `Principia/Architecture/Star32ConsecutiveKernel.lean`.

All five translations pass strict typed equivalence. The definitions `rightSection R y := fun x => R x y` and `leftSection R x := fun y => R x y` give exactly the two sectional class identities in ·11 and ·111. In PM's contextual-description notation, `E!` asserts that the displayed incomplete symbol has a value; ·12 and ·121 reconstruct this as an explicit class-extension witness equal to the corresponding section. For ·132, the typed reading of `A →R y` is `A = rightSection R y`, so the Lean biconditional retains the printed chain between sectional application, the section value, and the class abstract; the middle and first readings coincide by the adopted sectional-function interpretation.

No item is refused. Each proof is definitional or constructs its displayed section directly, so the accepted Lean proof bodies have no direct numbered-proposition references; both recorded dependency graphs are therefore empty for this lot. The five records are promoted in place to `awaiting-ci`; CI evidence remains pending.
