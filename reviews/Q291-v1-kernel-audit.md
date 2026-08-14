# PM I ✱13 Q291 v1 kernel audit

This strict audit applies the same acceptance boundary as the canonical ✱2
formalization: a printed assertion requires PM object syntax and a kernel-checked
`PM.Derivation`.  A Lean `Prop` theorem may support the mathematics, but it is
not the primary certificate.  The five `Star13Q291Targets` declarations return
only `Raw`; none returns `PM.Derivation` or `PM.FormedDerivation`.

The obstruction is structural under the T1–T9 gate. PM defines identity through quantification
over predicative propositional functions and then uses reducibility to extend
substitution to arbitrary functions.  The elementary v1 syntax has no ramified
function binder or identity constructor carrying that definition.  In ·11 the
entire function-quantified member is therefore an opaque `Raw` parameter; in
·12–·14 identity and function values are unrelated elementary atoms; in ·15
even `x = x` is supplied as an arbitrary atom.  These are useful target shells,
not assertions.

## Printed source graph, rebuilt from the demonstrations

- ✱13·11 cites ✱10·22, ✱13·1, ✱13·101, ✱1·7, and
  ✱10·11·21; the displayed proof also names `Transp` and `Comp`.
- ✱13·12 cites ✱13·101 and uses `Comp` followed by `Transp`.
- ✱13·13 is printed with ✱13·101, `Comm`, and `Imp`.
- ✱13·14 is printed with ✱13·13 and ✱4·14.
- ✱13·15 is printed with `Id` (✱2·08), ✱10·11, and ✱13·1.

The numbered citations remain in `printed_dependencies`.  The named proof
methods are recorded here rather than fabricated as theorem IDs.  Since every
Lean declaration is a syntax constructor and calls no PM proof theorem, all
five normalized PM dependency lists are empty. The four composite Raw targets
call only `CanonicalOrderedAdapters.rawImp`, which is recorded as their actual
Lean syntax dependency; ·15 merely returns its supplied atom. No historical
relaxation is claimed: each item remains blocked until a complete
syntax-and-object-derivation certificate exists. The explicit level is
`pm-syntax-target`, never `pm-derivation-v1`.
