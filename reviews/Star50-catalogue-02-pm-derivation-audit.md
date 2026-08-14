# ✱50 catalogue-02 PM-derivation audit

This cumulative five-item audit applies T1–T9 after rereading `dialogue.md`.
The existing declarations remain useful typed semantics, but none is a primary
PM derivation.

## Verdict

No item reaches `pm-derivation-v1`. ✱50·13, ·14, and ·15 are propositions in
Lean's host `Prop` (existence and uniqueness statements). ✱50·16 and ·17 are
equalities between predicate-valued functions. The active repository contains
no relational formula AST, concrete reading, or inductive derivation judgement
covering these printed formulas and their cited ✱10/✱13/✱14/✱30/✱50 routes.
Consequently T3 and T4 fail for all five; no `Support`, primary `Prop`
certificate, or ad hoc constructor has been introduced.

The targeted kernel audit separates a further fact: ·13, ·14, and ·15 use no
global axioms, whereas ·16 and ·17 depend on `propext` and `Quot.sound` through
the private predicate-extensionality lemma `classExt`. Thus ·16 and ·17 additionally fail
the axiom-free T5 gate. All five items are returned to `prepared` and retain
their current declarations only as secondary typed lemmas.

## Dependency graphs rebuilt from zero

The printed graph is:

- ·13 cites ✱13·19, ✱10·24, and ✱50·1;
- ·14 cites ✱30·3, ✱50·1, and ✱10·11;
- ·15 cites ✱50·14, ✱14·21, and ✱10·11;
- ·16 and ·17 display no bracketed citation.

The actual Lean declaration graph has ·13, ·14, ·15, and ·16 call `I`; ·17
calls no numbered ✱50 declaration. In addition, ·16 and ·17 call the private
implementation lemma `classExt`, which is not a catalogued PM proposition and
therefore produces no normalized catalogue edge. Normalization remains
·13→·01, ·14→·01, ·15→·01, ·16→·01, and no edge for ·17. Existing relaxation
records preserve the mismatch between the printed proof routes and the direct
semantic implementation; no edge is inferred from prose.
