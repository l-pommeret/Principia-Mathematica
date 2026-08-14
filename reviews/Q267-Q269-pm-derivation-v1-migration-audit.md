# Q267–Q269 strict `pm-derivation-v1` migration audit

Scope: ✱10·2, ·21, ·23, ·24, and ·25.  The mandatory standard is
`Principia/FirstEdition/Volume1/Part1/SectionA/Star2.lean`, together with the
T1–T9 gates recorded in `dialogue.md`.

All five catalogued declarations are in the import closure and their current
Lean constants are axiom-free.  That is necessary but not sufficient for a PM
derivation.  None is declared as a `theorem` (T2), and none has a companion
`*_reading` value connecting its exact printed string to a parsed PM formula
(T4).

The endpoint types also give the following T3 results:

- ·2 and ·21 return `Star_10_2Assertion`, a theorem-specific `structure` whose
  endpoint connection is only `targetReading : target = target`;
- ·23 returns another theorem-specific `structure`, again ending in a
  reflexive `targetReading` field;
- ·24 returns the genuine inductive `OrderedAssertion` judgement for the
  explicit ✱9·1 instance.  This is useful object-calculus evidence, but the
  public declaration remains a `def` and has no reading for the printed ·24
  formula, so T2 and T4 still fail;
- ·25 returns a theorem-specific `structure`; its only endpoint connection is
  `reading : target = target`.

The printed citation graphs were retained independently from the source.  The
Lean call graphs were rebuilt from the public bodies:

- ·2 calls ✱10·1 and ✱10·11;
- ·21 calls ·2;
- ·23 calls ✱10·1 and ·21 (the `Star10Q265FinalPrerequisites.star_10_23`
  declaration appearing in the old metadata is not called by the body);
- ·24 calls the explicit ✱9·1 schema constructor
  `OrderedAssertion.star_9_1_instance`;
- ·25 calls ✱10·1 and ·24.

No `Support` wrapper or target-specific fake constructor occurs in these
modules.  No semantic `Prop` theorem is substituted for the missing PM
judgements, and the axiom-free result is recorded only as audit evidence.

Verdict: the five items are `prepared`, with
`formalization_level = pm-ast-component-certificate-v1`, and are blocked on
the missing theorem/reading/endpoint gates.  None receives
`pm-derivation-v1`.
