# Constrained reconstruction of printed PM demonstrations

The reconstruction pipeline treats the printed demonstration as a search
constraint, not merely as prose checked after a proof has been found.

1. `scripts/pm_syntax.py` parses a printed proposition into the PM object AST.
2. `scripts/pm_proof_skeleton.py` parses the demonstration into ordered
   references, printed aliases, substitutions, and intermediate-line uses.
3. `scripts/pm_constraint_manifest.py` resolves those references against the
   reviewed item metadata and emits two deliberately distinct sets:

   - `allowed_pm_items` / `allowed_lean_declarations`: the only historical
     results that a reconstructed proof may cite;
   - `context_closure` / `context_declarations`: declarations that must be
     present merely so that the allowed results typecheck in an isolated
     sandbox.

The context closure grants no proof permission. A generated Aristotle request
must state the whitelist explicitly, and the returned term must still pass the
repository dependency audit. Thus the prompt constrains search and the audit
independently checks the resulting term.

Strict compilation fails before submission when a printed reference has no
metadata, is not kernel checked, or an alias cannot be resolved at the current
historical locus. Family aliases such as `Transp` remain explicit finite
families rather than being silently resolved to whichever theorem happens to
close the goal.

Substitutions are retained as first-class audit data. In the elementary
fragment they may be implemented by instantiation of Lean schema parameters,
as documented in `docs/SUBSTITUTION.md`; the manifest nevertheless records the
printed substitution instead of erasing it.

## Failure and relaxation

If the strict whitelist does not close the goal, that outcome is evidence. A
later relaxation must produce a second manifest recording every added item;
the strict failure is never overwritten. This supports three distinct
editorial outcomes:

- strict closure: reconstruction faithful to the printed citations;
- alias-family closure: faithful up to a printed named family;
- relaxed closure: printed dependency list incomplete, with the minimal added
  dependencies recorded explicitly.

The current manifest compiler is the deterministic boundary. Automatic prompt
rendering and minimal-relaxation search may be built on it, but must not merge
proof permissions with implementation closure.
