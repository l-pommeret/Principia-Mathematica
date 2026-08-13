# Q222 continuation — replace forbidden placeholders only

The preceding archive is definitively rejected: its `Q222.lean` contains
`sorry`, `admit`, and `Classical`.  The returned source file must contain none
of `sorry`, `admit`, `axiom`, `unsafe`, or `Classical` anywhere.

Keep the approved event-based construction.  In ✱3·22, retain actual calls to
✱3·13, Perm/✱1·4, ✱3·14, final Transp, and replace only the unresolved holes
by explicit `star_2_06` and `PM.Derivation.detach` applications.  The only
allowed non-printed additions in the whole batch are: ✱2·32 for ✱3·2’s
association gap, and exactly two ✱2·06 uses for ✱3·22’s implicit syllogistic
composition; detach is ✱1·11 when used.  No other dependency is permitted.

Preserve the other targets and all `PM-Q222-DEPS` audit comments.  Do not
weaken targets or add any theorem/axiom/shortcut.  Return complete Lean terms.
