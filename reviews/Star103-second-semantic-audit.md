# ✱103 second strict semantic audit

Scope: exactly the next five prepared candidates after the opening audit:
✱103·1, ·16, ·22, ·23, and ·301. Each diplomatic formula was compared with
the same-number declaration in `Star103Kernel.lean` or
`Star103Kernel2.lean`. Items ·31 and later remain unaudited in this wave.

All five candidates are refused; none is promoted to `awaiting-ci`:

- ✱103·1 is a four-term equality chain for homogeneous-cardinal expressions;
  Lean's `star_103_1` is the definitional equivalence between
  `CardinalClass s t` and `Equinumerous s t`.
- ✱103·16 compares equality involving `N₀cʻα` and `Ncʻβ`; Lean's
  `star_103_16` turns an `Equinumerous s t` hypothesis into the definitionally
  identical proposition `CardinalClass s t`.
- ✱103·22 derives existence and uniqueness of `μ` from `μ ∈ N₀C`; Lean's
  `star_103_22` proves symmetry of represented-cardinal membership.
- ✱103·23 states that the empty class is not in `N₀C`; Lean's
  `star_103_23` only unfolds represented-cardinal membership to
  equinumerosity.
- ✱103·301 identifies the type-indexed `NCᵅ(α)` and `N₀C(α)`; Lean's
  `star_103_301` instead characterizes equality of two `CardinalClass`
  predicates by equinumerosity of their representatives.

The Lean declarations belong to the same simplified surrogate model as the
first wave, but none retains the printed hypotheses, operators, or conclusion.
Each catalogue record therefore remains `prepared` with an explicit semantic
refusal and no CI promotion.
