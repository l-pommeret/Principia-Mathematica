# ✱38 catalogues 03–04 strict semantic review

Scope: the six remaining ✱38 items, ·21, ·22, ·23, ·24, ·3, and ·31,
checked against the diplomatic transcription of printed page 313 and the
signatures in `Star38Kernel.lean`.  Exactness is assessed only within the
explicit typed, total-binary-function abstraction used by this kernel.

## Exact targets

·21 preserves the complete slice-comprehension equality.  ·22 preserves both
equalities in the printed three-term chain.  ·23 preserves both conjoined
definedness assertions; under the declared total abstraction the two slice
terms directly inhabit `Class γ`.  ·24 preserves both directions of the
nonemptiness equivalence, with an element of the slice corresponding exactly
to an element of `α`.  None drops a premise, conjunct, witness, equality, or
case, and none assumes its target.

All four proofs close from the local definitions or elementary witness
construction without invoking numbered theorem constants.  Their printed
citations are therefore retained as audited `relaxed-closure` history, with no
dependency added beyond print.  Verdict: ·21, ·22, ·23, and ·24 are promoted to
`awaiting-ci`.

## Refused targets

·3 prints a three-term equality chain.  `star_38_3` states only the equality
between the family image and the first comprehension; it omits the second
equality whose predicate uses `♀yʻʻα`.  Definitional convertibility does not
repair a missing term in the declared proposition.

·31 prints four equal presentations.  `star_38_31` states a single equality
between the outer image and the comprehension using the right-section image.
It omits the intervening comprehension using `α♀_{,,}y` and the final
triple-image presentation `♀yʻʻʻκ`.  Again, reducibility of internal
definitions cannot make the narrower theorem signature source-exact.

Verdict: ·3 and ·31 remain `prepared` and are blocked as
`blocked-semantic-target-incomplete`.  They are isolated from the homogeneous
`awaiting-ci` batch so that no refused item is accidentally promoted.
