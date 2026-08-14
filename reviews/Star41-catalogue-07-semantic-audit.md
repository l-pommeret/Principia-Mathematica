# ✱41 catalogue 07 strict semantic audit

The five restriction laws ✱41·34–351 were checked statement by statement
against `Star41RestrictionKernel.lean`. `mapRelations` and `mapClasses` retain
the original class membership witness, while `sumRelations` and `sumClasses`
are genuine existential unions; none of these encodings collapses the source
claim.

✱41·34, ·341, and ·342 commute the relational sum with left, right, and
two-sided restriction respectively. ✱41·35 and ·351 commute the sum over a
class of restrictions of one fixed relation with right and left restriction by
the class sum. Each equality is proved pointwise in both directions without an
extra premise. All five are exact typed reconstructions and are promoted to
`awaiting-ci`.
