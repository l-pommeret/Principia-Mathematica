# ✱122 catalogue 01 strict semantic audit

Scope: exactly PM2:✱122·01, ·1, ·11, ·12, and ·14 on first-edition
printed pages 256–257 (scan leaves 296–297). The displayed statements were
checked against Project Gutenberg 78255 and compared declaration by declaration
with `Principia/Architecture/Star122Kernel.lean`. The theorem-name correspondence
is not treated as evidence of semantic equivalence.

No item is promotable to `awaiting-ci`.

- **✱122·01.** PM defines `Prog` as the intersection of one-one relations with
  relations whose domain is the ancestral of their first member. Lean instead
  defines a `Progression` structure with five fields: functionality, injectivity,
  a custom reachability linearity condition, range/domain inclusion, and a
  two-cycle prohibition. `star_122_01` merely repackages those fields as a
  conjunction. It neither represents nor proves the printed definition.
- **✱122·1.** The source unfolds ✱122·01 into an equivalence involving
  one-one relations, domain, the first member `BʻR`, and the ancestral. Lean
  projects only `Functional R ∧ Injective R` from its replacement structure;
  the defining domain/ancestral equality is absent.
- **✱122·11.** PM adds the descriptive-symbol existence condition `E!BʻR`
  and a pointwise characterization of the domain by the ancestral. Lean returns
  the unrelated field `Linear R`. None of first-member existence, domain, or
  ancestral membership occurs in its target.
- **✱122·12.** PM characterizes progressions through every class closed under
  the converse relation and containing the first member. Lean is just the
  implication `Progression R → Linear R`. It has no class parameter, closure
  condition, first member, or domain characterization.
- **✱122·14.** PM identifies the posterity of the first member under the
  converse relation with the converse domain. Lean projects
  `range R ⊆ domain R`; equality, posterity/ancestral closure, converse, and
  the first member are all missing.

The accepted Lean dependency graph is therefore empty for every item. The
printed dependency graph is recorded in the catalogue where the displayed
proof explicitly cites predecessors: ✱122·1 depends on ✱122·01; ✱122·12 cites
✱122·11 and ✱90·1; ✱122·14 cites ✱122·1, ✱37·25, and ✱91·52. No
local declaration is accepted merely because it compiles, so all five records
remain `prepared` with explicit semantic-block classifications.
