# ✱38 catalogue-02 strict semantic review

Scope: exactly ·11, ·12, ·13, ·131, and ·2, compared with the diplomatic
transcription on printed page 313 and their declarations in
`Star38Kernel.lean`.  As in catalogue-01, exactness is asserted only under the
declared typed abstraction `op : α → β → γ`; it is not a claim that Lean's
total functions model every contextual-description convention of PM.

All five targets are exact in that scope.  ·11 retains both printed equalities
and identifies both section applications with `op x y`.  ·12 retains the
conjunction of both definedness assertions: total application supplies
`op x y : γ` as the witness on each side.  ·13 and ·131 preserve the full
membership biconditionals, including the existential witness, class-membership
condition, and equality.  ·2 is exactly the defining equality between the
slice and the image of the right section.  No premise, conjunct, quantified
variable, equality, or requested case is omitted, and no proof assumes its
target.

Each declaration closes by unfolding `LeftSection`, `RightSection`, `Image`,
or `Slice`, rather than by invoking a numbered theorem.  Accordingly all five
Lean dependency lists are empty.  The metadata records every printed citation
as an audited `relaxed-closure` historical dependency; no dependency beyond
print is introduced.

Verdict: promote exactly these five items to `awaiting-ci`.  No item from a
later ✱38 catalogue is covered by this review.
