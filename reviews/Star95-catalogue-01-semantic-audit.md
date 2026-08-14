# ✱95 catalogue 01 strict semantic audit

The first five printed loci of ✱95 (·01, ·1, ·11, ·12, and ·13) were
transcribed in order from Project Gutenberg 78050 and checked against the
1910 Volume I witness, printed page 627 (scan leaf 649). The batch is a
duplicate-free 5/5 source↔Lean mapping.

The typed relation model preserves PM's generator `M ↦ P|M|Q` as
`comp (comp P M) Q`. `Equi` is its inductively generated least class, and
·1 proves the source's universal least-closed-class characterization in both
directions. Thus ·01 and ·1 are extensionally exact, rather than merely
suggestive encodings. Proposition ·11 is exactly the corresponding invariant
induction rule. Proposition ·13 is exactly membership of the seed.

The former Lean statement for ·12 required the caller to provide a predecessor
and an equality explicitly, which was strictly weaker than PM's quantified
claim over every member outside the singleton seed. It was repaired by case
analysis on `Equi`: the base case contradicts `N ≠ R`, while a step is exactly
the assumed transformed-member case. The repaired declaration now matches the
source quantifiers and conclusion without an additional mathematical
hypothesis. Consequently all five items pass strict equivalence and are marked
`awaiting-ci`; none is refused and none is marked `kernel-checked` before CI.

The printed and Lean dependency graphs are recorded separately. PM's proofs
route through ancestral/image and earlier propositional-calculus results;
Lean's inductive presentation closes ·1, ·12, and ·13 through constructors or
elimination, while ·11 retains the exact ·1 edge. Each omitted historical edge
is therefore documented as a reviewed relaxed closure, not silently erased.
The deterministic parser does not yet cover PM's equi-factor/ancestral
notation, so all five records carry `reviewed-gap` evidence here.
