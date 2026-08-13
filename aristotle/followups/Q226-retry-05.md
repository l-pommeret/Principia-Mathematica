# Q226 final verification and bounded correction

Audit the immediately preceding retry-04 archive and correct only demonstrated violations.

- `star_3_45` may use only the documented `PM1:✱3·3` implicit-exportation relaxation.
- `star_3_47` must call local `star_3_45` as its Fact; it may use `✱3·2` only in the exact `Γ=[]` branch and `✱3·03` only in the nonempty-context branch.  No direct `star_3_3`.
- No delivered Lean source may contain direct `PM.Derivation.star_1_5` or `_1_6`, `syllRuleQ220`, axioms, `sorry`, `admit`, or `unsafe`; `Classical` is permitted only if unused in the Main harness.
- Preserve every manifest whitelist, dependency, and prior approved relaxation.  Do not introduce any permission or citation.

Return literal-source scans, exact citation ledger, and axiom evidence.  If retry-04 already conforms, make no proof broadening: verify the exact whitelist and report it.
