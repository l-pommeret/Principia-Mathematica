# Q220 follow-up — make ✱2·83 use the printed ✱2·82 citation

Keep every accepted declaration and proof in `RequestProject/Q220.lean`, except
replace only the body of `PM.FirstEdition.Volume1.Star2.star_2_83`.

The current body calls `star_2_82_rightAssociated`, so the machine audit marks
the printed event `[✱2·82 (∼p,∼q)/(p,q)]` uncovered. Reconstruct the same exact
target by calling the already proved, required declaration `star_2_82` and then
using only the associativity apparatus already justified by the Q220 result:
`star_2_31`, `star_2_32`, `star_2_05`, `star_2_06`, and
`PM.Derivation.detach`. Preserve the printed simultaneous substitution.

Do not call `star_2_82_rightAssociated`, `star_2_8`, or `star_2_81` in the
transitive helper closure of `star_2_83`. Do not change its statement, weaken
the target, add an axiom, use semantics, `Classical`, `sorry`, `admit`, or
`unsafe`. Return the complete updated project file and ensure Lean checks it.
