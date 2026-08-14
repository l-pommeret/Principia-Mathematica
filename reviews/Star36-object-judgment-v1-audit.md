# ✱36 opening — object-language/kernel-judgment v1 audit

Scope: exactly ✱36·01, ·11, ·13, ·2, and ·201. The acceptance standard
is the `Star2` architecture: a source theorem must have a PM formula object (and
an explicit printed reading where applicable) together with a proof whose type
is a kernel-recognized PM judgment such as `PM.Derivation Γ formula`. A host
`Prop` theorem may remain useful secondary evidence but cannot establish
canonical formalization by itself.

## Result

All five items are blocked at v1. `Star36RestrictionKernel.lean` defines
`Class` as `α → Prop`, `Relation` as `α → α → Prop`, and proves equalities or
iff statements between those semantic functions. It imports neither
`Principia.Deduction.System` nor `Principia.Syntax.Printed`; it constructs no
PM formula, no `ElementaryReading`/printed formula, and no `PM.Derivation` (or
other recognized kernel judgment). In contrast, `Star2` separates the formula
object, reading, printed demonstration, and a theorem whose conclusion is a
derivation judgment.

- **✱36·01** has only an extensional host definition and equality theorem; the
  PM definition object and its definition judgment are absent.
- **✱36·11** calls the host theorem ·01, preserving the secondary equality but
  not asserting a PM formula in the kernel.
- **✱36·13** is `Iff.rfl` after unfolding the host function. This validates the
  semantic gloss but does not reconstruct the printed uses of ✱36·11 and
  ✱35·102.
- **✱36·2** proves the semantic equality by `funext`/`propext`; it does not
  instantiate the printed ✱35·15 theorem inside the PM deductive system.
- **✱36·201** independently repeats host extensionality rather than deriving
  the PM assertion from printed predecessor ✱36·2.

## Dependency audit

Gutenberg prints ✱36·01 at ·11; ✱36·11 and ✱35·102 at ·13;
✱35·15 at ·2; and ✱36·2 at ·201. The only actual numbered call in
the secondary Lean bodies is ·11 → ·01. The other missing edges are recorded
as historical closure differences, explicitly as evidence of incompleteness.

No item is canonical, kernel-checked, or CI-eligible under the v1 standard.
Completing any item requires the object-language relation/restriction syntax,
its printed interpretation, and a kernel derivation following the cited PM
route; strengthening the wording around the existing `Prop` theorems cannot
remove this block.

## Targeted axiom and graph recheck

`#print axioms` confirms that only the secondary pointwise equivalence ·13 is
axiom-free. The extensional host equalities ·01, ·11, ·2, and ·201 depend on
Lean's `propext` and `Quot.sound`; they therefore cannot serve as the requested
axiom-free object-relation certificates. The dependency extractor independently
reconfirms that the sole actual numbered call is ·11→·01. The bodies of ·13,
·2, and ·201 call no historical theorem, so their missing printed routes are
not silently normalized away. This recheck leaves all five correctly
`prepared` and blocked.
