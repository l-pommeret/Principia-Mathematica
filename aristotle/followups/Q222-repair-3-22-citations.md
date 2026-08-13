# Q222 continuation — repair printed-event coverage for ✱3·22

The immediately preceding relaxed archive is rejected, not for the approved
✱3·2 associativity relaxation, but because its ✱3·22 proof bypasses the
printed citations ✱3·13 and ✱3·14.  Preserve byte-for-byte the conforming
proofs of ✱3·2, ✱3·21 and ✱3·24 (including the sole ✱2·32 relaxation in
✱3·2).  Repair only `star_3_22`.

Its term must explicitly use, in the printed route, all of:

1. `star_3_13 q p` for `[✱3·13 (q,p)/(p,q)]`;
2. `PM.FirstEdition.Volume1.Star1.star_1_4` for `[Perm]`;
3. `star_3_14 p q` for `[✱3·14]`;
4. exactly an appropriate ✱2·15/16/17 `Transp` form for the final step.

Use `PM.Derivation.detach` only when needed and make it auditable as ✱1·11.
Do not introduce ✱1·5, ✱1·6, ✱2·32 outside ✱3·2, or any other new dependency.
Do not close ✱3·22 directly from Perm/Transp.  Put these named theorem calls in
the actual proof term, not comments or unused `have`s.  Each target must keep
the `PM-Q222-DEPS` line separating printed dependencies, added dependency, and
detachment convention.  No axioms, Classical, semantics, sorry/admit/unsafe,
or target changes.
