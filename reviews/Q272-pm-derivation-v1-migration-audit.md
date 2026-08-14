# Q272 strict `pm-derivation-v1` migration audit

Scope: ✱10·39, ·4, ·41, ·411, and ·412, using
`Principia/FirstEdition/Volume1/Part1/SectionA/Star2.lean` as the mandatory
standard.

`Star2.lean` proves an object-language `Elementary` formula by returning the
judgement `PM.Derivation formula`; its theorem type itself is the asserted PM
formula.  None of the five public Q272 declarations meets that standard.
Each currently returns a theorem-specific structure in `Prop`.  Its fields
contain earlier component certificates or elementary derivations, but the only
connection to the displayed `Raw` endpoint is
`targetReading : target = target`.  There is no field of type
`Derivation target`, `OrderedAssertion target`,
`CanonicalOrderedAssertion target`, or another conservative assertion
judgement whose indexed carrier embeds as that target.

The component graphs were reconstructed directly from the Lean bodies:

- ·39 calls ✱10·22, ✱3·47, and ✱10·27;
- ·4 calls ✱10·22 and the component package ·39;
- ·41 calls ✱10·1 and the composed ✱10·11·21 action (indexed as its existing
  ✱10·11 component in the current registry);
- ·411 calls ✱4·39 and the same composed generalization action;
- ·412 calls ✱4·11 and ✱10·271.

These calls prove fields of the surrounding `Prop` structures; they do not
compose into an assertion of the displayed targets.  The printed citation
lists remain independently recorded in metadata, including their existing
explicit normalization of compound citations.  No semantic `Prop` theorem is
promoted as a substitute.

Verdict: all five items return to `prepared` with
`formalization_level = pm-ast-component-certificate-v1` and are blocked on a
real PM endpoint judgement.  In particular none receives
`pm-derivation-v1`.  The existing Lean module remains useful secondary
evidence and still kernel-checks, but its compilation cannot establish the
missing judgement.

