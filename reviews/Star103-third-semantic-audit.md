# ✱103 third strict semantic audit

Scope: exactly five candidates: ✱103·31, ·32, ·33, ·34, and ·4. The source
formulas were compared with the declarations bearing those numbers in
`Star103Kernel2.lean`.

All five are refused. ✱103·31 replaces a unique-existence implication with a
homogeneity conclusion. ✱103·32, ·33, and ·34 replace printed class inclusions
involving `NC`, `N₀C`, and removal of `ιʻΛ` with facts about equality or
equinumerosity of represented cardinal classes. ✱103·4 replaces the printed
`sm`-image identity with an equivalence between `SameCardinalClass` and
`Equinumerous`. None preserves the printed operators and conclusion.

The actual Lean-only numbered dependencies are recorded in the catalogue, but
they do not repair the semantic mismatch. No candidate is promoted to
`awaiting-ci`.
