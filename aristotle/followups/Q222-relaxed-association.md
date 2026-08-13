# Q222 continuation — documented minimal associativity relaxation

The first Q222 archive is rejected as a **strict** reconstruction.  Preserve
that rejection: ✱3·12 is `((∼p ∨ ∼q) ∨ (p . q))`, while ✱3·2 is
`∼p ∨ (∼q ∨ (p . q))`; the printed direct citation omits this reassociation.
The historical audit is `reviews/Q222-association-audit.md`.

Continue this same project only under the expressly approved classification
`relaxed-associativity-gap`.  Produce the four declarations in their existing
order and targets, with no new axioms, Classical, semantics, `sorry`, `admit`,
unsafe declarations, or target changes.

For ✱3·2, use **exactly** ✱3·12 followed by ✱2·32 at the required instance;
use ✱1·11/detach only to apply that implication.  This is the sole added
historical proposition beyond its printed citation.  Do not use ✱1·4, ✱1·5,
✱1·6, or any other primitive/theorem.

For every target, include a short adjacent comment of the form `PM-Q222-DEPS`
that separates (a) printed citations, (b) the explicitly added relaxation
dependencies, and (c) the detachment convention when it is actually used.
The permitted sets are:

- ✱3·2: printed ✱3·12; added ✱2·32; detach = ✱1·11 only if present.
- ✱3·21: printed ✱3·2 and Comm/✱2·04; added none; detach = ✱1·11 only if present.
- ✱3·22: printed ✱3·13, Perm/✱1·4, ✱3·14 and Transp/one of ✱2·15–17; added none; detach = ✱1·11 only if present.  Do not add ✱1·5 or ✱1·6.
- ✱3·24: printed ✱2·11 and ✱3·14; added none; detach = ✱1·11 only if present.

If any target needs another dependency, stop and report it rather than adding
it.  The output must make every actual theorem occurrence auditable.
