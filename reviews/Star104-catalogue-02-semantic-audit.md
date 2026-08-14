# PM II ✱104 catalogue-02 strict semantic audit

This audit covers exactly the next five canonical formulas after Q427:
✱104·011, ·021, ·031, ·1, and ·101.  None passes strict equivalence.

- The definitions ·011 and ·031 require explicit intersections with their
  second-higher type domains.  Their Lean namesakes merely unfold `Asc2` to
  `EquivSet` and do not contain either intersection.
- Definition ·021 identifies `N²C` with the domain of `N²c`; its Lean namesake
  is again only `Asc2 s u ↔ EquivSet s u`.
- Proposition ·1 gives two successive characterizations of membership in
  `N¹cʻα`, including the higher-type membership/subset restriction.  The Lean
  namesake proves only that `Asc` abbreviates `EquivSet`.
- Proposition ·101 requires both similarity to `α` and inclusion in `tʻα`.
  Its Lean namesake retains only equinumerosity, so its converse admits classes
  at the wrong type level.

All five are therefore recorded only in the refusal manifest.  No
`awaiting-ci` catalogue is created, and no nearby theorem is substituted for
the printed target.
