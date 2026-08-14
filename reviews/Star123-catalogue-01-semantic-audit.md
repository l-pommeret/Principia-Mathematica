# ✱123 catalogue-01 semantic audit

This strict item-level audit covers exactly the first five loci on printed page
269 (scan leaf 309), checked against PG78255 and the 1912 Volume II witness.

Three declarations are exact and are therefore the only items promoted to
`awaiting-ci`:

- ✱123·01 defines `AlephZero` as the class of precisely those classes that are
  domains of progressions; the Lean equality is extensional and definitional.
- ✱123·1 states both directions of membership in `AlephZero`, with exactly one
  existentially quantified progression and equality to its domain.
- ✱123·101 constructs the source's existential witness from an arbitrary
  progression and proves exactly that its domain belongs to `AlephZero`.

✱123·02 is refused because the typed architecture does not yet represent the
source's cardinal intersection and `t₀` operations. In particular, translating
the displayed equality as a conjunction would silently change the formula.

✱123·11 is refused. Its printed derivation uses ✱122·1 in the direction from a
one-one relation satisfying the displayed domain/backward-closure equation to a
progression. The current `Star122Kernel.star_122_1` exposes only the forward
projection `Progression R → Functional R ∧ Injective R`; it neither represents
the backward-closure equation nor proves the required converse. Adding
`Progression R` as a Lean premise would assume the missing conclusion and
therefore would not be an exact formalization.

### Dependency extraction repair

The source-level dependency extractor finds no theorem call in either exact
declaration ✱123·1 or ·101: the former is `Iff.rfl` after unfolding
`AlephZero`, and the latter constructs its existential progression witness
directly. Their `lean_dependencies` and `normalized_dependencies` are therefore
empty. The printed citations remain intact in `printed_dependencies` and are
recorded as `printed_but_unused` under explicit `relaxed-closure` records; this
preserves PM's historical proof routes without inventing Lean call edges.

Targeted local checks succeeded for `Star123OpeningKernel`, `Star123Source`, and
the root `Principia` module under the pinned toolchain. Online CI evidence is
intentionally still pending.
