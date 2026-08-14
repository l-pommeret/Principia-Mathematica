# ✱114 catalogue 02 strict semantic audit

Scope: exactly PM2:✱114·21–·25, checked against Project Gutenberg 78255
and first-edition p. 125 / scan leaf 165. Three typed reconstructions pass;
two correspondences are refused.

Accepted as exact typed reconstructions:

- **✱114·22:** the unique factor is empty, so the singleton-indexed
  dependent product has no inhabitant. This is precisely the type-level
  reading of the printed product cardinal being zero.
- **✱114·23:** an empty coordinate eliminates every dependent choice
  function, exactly expressing that a family containing an empty factor has
  zero product cardinal.
- **✱114·24:** restriction of a choice function along the subfamily
  inclusion preserves existence, the typed content of non-nullity descending
  from `λ` to `κ ⊂ λ`.

Refused:

- **✱114·21:** PM states equality of cardinal objects. Lean retains only an
  iff between `Nonempty` propositions, which is a strictly weaker invariant
  and cannot establish cardinal equality.
- **✱114·25:** PM identifies the multiplicative axiom with a universally
  quantified zero-product criterion. Lean uses ambient `Classical.choice` to
  build a witness for one family from pointwise `Nonempty`; it neither exposes
  the axiom as a proposition nor proves the printed biconditional.

The three accepted declarations have empty Lean theorem-dependency graphs;
·22 and ·23 discharge their printed citations directly in the typed model,
as recorded by explicit relaxed-closure annotations. Only those three items
are marked `awaiting-ci`.
