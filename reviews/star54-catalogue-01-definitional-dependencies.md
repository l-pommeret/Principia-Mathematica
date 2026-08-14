# ✱54·1, ·101, ·102 definitional dependency audit

The three printed citations are definitional readings, not additional Lean
theorem calls. `Zero` and `Two` unfold to the displayed class predicates, so
the exact proof terms are respectively `rfl`, `Iff.rfl`, and `Iff.rfl`.
Dependency extraction is therefore correctly empty while the printed
citations remain recorded as reviewed unused dependencies.
