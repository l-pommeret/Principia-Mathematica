# ✱103 fourth strict semantic audit

Scope: exactly five candidates: ✱103·42, ·43, ·44, ·5, and ·51. This exhausts
`PM2-star-103-Q426.json` without extending the audit beyond ✱103.

All five are refused. The Lean declarations ·42 and ·43 prove symmetry and
transitivity of equality between represented `CardinalClass` predicates,
whereas print concerns the `sm` relation and an `sm`-image/intersection
identity. Lean ·44 relates `SameCardinalClass` to `CardinalClass`, omitting the
printed hypotheses `μ,ν ∈ N₀C` and both `sm`-image equalities. There is no
`star_103_5` declaration for the printed assertion `0 ∈ N₀C`. Finally, Lean
·51 proves homogeneity of two represented cardinal classes from equinumerosity,
not the printed assertion `1 ∈ N₀C`.

No formula in this lot has an equivalent Lean target, so all remain
`prepared` with explicit refusals and none enters `awaiting-ci`.
