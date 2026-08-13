# Q226 continuation — two exact, locus-scoped relaxations only

Reconstruct all four required declarations in the same project.  The prior
retry is rejected and must not be reused as source.

1. **PM1:✱3·45 only.** `PM1:✱3·3` (`Exp`) is authorized exactly for the
   printed `Syll` compositions based on kernel `✱3·33`/`✱3·34`, classified
   `incomplete-printed-inference/implicit-exportation-gap`.  Use no `Comm` in
   ✱3·45; its printed events remain Syll, Transp, Id, ✱1·01, ✱3·01.
2. **PM1:✱3·47 only.** Its sole exceptional permission is `PM1:✱3·2`,
   `context-polymorphism-gap`, and only in the `Γ = []` branch.  Its nonempty
   branch must use printed `✱3·03`.  The body of `star_3_47` must call the
   already-proved local theorem `star_3_45` for each printed `Fact` event and
   must contain **no direct reference, invocation, or local helper based on
   `PM1:✱3·3` / `star_3_3`**.  The fact theorem’s documented dependency does
   not grant a direct permission to this target.

No other extra PM item or inference is authorized.  The remaining targets
must remain within their manifest whitelists.

## Literal hygiene for all delivered Lean sources

Do not carry over the old generated context.  Build/import a minimal audited
context in which no delivered Lean file other than the pre-existing unused
`RequestProject/Main.lean` contains `Classical`.  In every delivered support,
context, proof, and audit file, prohibit `PM.Derivation.star_1_5`,
`PM.Derivation.star_1_6`, `syllRuleQ220`, `axiom`, `sorry`, `admit`, `unsafe`,
and every unlisted PM theorem.  References to the permitted theorem-items
`PM.FirstEdition.Volume1.Star1.star_1_4` or `star_1_6` are allowed only where
those are in the target manifest; never use the primitive constructors.

Return a literal per-file token scan and a direct-citation ledger per target.
The ledger must separately prove that `star_3_47` has zero direct `star_3_3`
occurrences.  Do not replace targets with semantic obstructions.
