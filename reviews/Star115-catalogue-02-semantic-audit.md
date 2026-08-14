# ✱115 catalogue 02 — strict source/Lean semantic audit

Scope: the next five loci of PM II ✱115 (·12, ·13, ·131, ·14, and
·141), in printed order on page 137 (1912 scan leaf 177), checked against
Project Gutenberg 78255 and the first-edition scan. The full theorem types,
not their names or general subject, determine promotion.

All five candidates are refused:

- ✱115·12 asserts cardinal-class membership and similarity of the whole
  multiplicative class with the diagonal membership relation. Lean supplies
  only dependent-function extensionality.
- ✱115·13 asserts an equinumerosity of two entire classes. Lean weakens this
  to an iff between two `Nonempty` propositions.
- ✱115·131 states a class equality under `α ≠ β`. Lean again proves only
  inhabitation equivalence and does not represent the premise.
- ✱115·14 characterizes membership of every product element by an explicit
  union decomposition under a disjointness alternative. Lean proves only
  nonemptiness equivalence and omits both the element and the premise.
- ✱115·141 equates two unions/supports when the product exists uniquely.
  Lean concludes only the tautology `I = I` from product inhabitation.

The split is therefore homogeneous: 0/5 promoted and 5/5 recorded in the
refused manifest as `prepared` / `blocked-semantic-mismatch`. There is no empty
awaiting-CI manifest. All five Lean declaration-level dependency graphs are
empty; the printed historical citations remain recorded independently. No
locus in this lot duplicates catalogue 01.

The deterministic notation parser does not cover these uses of `Prod`,
similarity, higher-order cardinal classes, scoped connectives, or class union,
so every record carries `reviewed-gap` evidence pointing to this audit.
