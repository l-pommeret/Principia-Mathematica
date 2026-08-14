# ✱9 PM migration — lot 01

Scope: `PM1:✱9·1`, `PM1:✱9·11`, `PM1:✱9·12`, `PM1:✱9·13`, and `PM1:✱9·2` only.

## Kernel evidence

- ✱9·1 and ✱9·11 are exact assigned-first-order AST targets in `FirstOrderPrerequisites`, certified by distinct primitive constructors of `OrderedAssertion`. They are not represented merely as Lean `Prop` theorems.
- ✱9·12 is the primitive assigned-order detachment constructor. ✱9·13 is the primitive capture-safe real-to-apparent generalization constructor over `Apparent.openHead`.
- ✱9·2 has the mixed-order `CanonicalOrderedFormula.Raw` target required by the print. `Star92KernelAssertion.printed_chain` stores a `Derivation` for its ✱2·1 line, the exact ✱9·1 instance, both Raw scope identities, and the ✱9·05/✱9·01 normalization witnesses. `Star92Kernel.derive` is the closed theorem-specific certificate; the public declaration only exposes it.

The ✱9·2 internal call is deliberately named `star_2_1`, matching the printed citation, rather than its definitional alias `star_2_08`. Direct wrapper dependencies remain separately recorded from the certificate's internal PM calls so the graph is neither inflated nor hidden.

## Dependency audit

The four primitive items have no printed premises and no Lean calls. For ✱9·2, the printed chain is ✱2·1, ✱9·1, ✱1·11, ✱9·05, ✱9·01, ✱1·01. The named kernel calls directly cover ✱2·1, ✱9·1, ✱9·05, and ✱9·01; the two logic laws occur as explicit certificate stages/normalization meaning rather than additional theorem calls. The public wrapper's only direct call is `Star92Kernel.derive`, which normalizes back to the item itself and is therefore excluded from its dependency edge set.

All five entries qualify for `pm-derivation-v1`: each has a PM AST, a PM judgement type, and a kernel-checked primitive or derived certificate. No proposition-only surrogate is used.
