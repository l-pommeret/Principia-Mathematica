# Q323 review — PM I ✱20·59–61

Leaf 228 / printed p. 206, SHA-256
`00ebce3fbb811f3b3bc84aeb2e09055c8153f894986e6f0269063a0a256a2612`,
and PG 78050 agree on all three uncited propositions.

`Star20Q323Kernel.lean` reuses the explicitly typed class carrier and
contextual class-description eliminator of ✱20·07–08.  ✱20·6 is the complete
class-quantifier duality theorem and uses `Classical.byContradiction` only for
its printed `¬∀¬ → ∃` direction.  ✱20·61 is unconditional universal
instantiation.  Both quantify over an arbitrary typed class carrier; neither
collapses classes into an untyped universe or assumes reducibility.

✱20·59 remains an exact target rather than a claimed assertion.  Its
`(ια)(fα)` is eliminated through `ClassDescriptionScope`; making it a freely
denoting Lean value would contradict PM's incomplete-symbol discipline.  A
proof needs the still unavailable assertion rules for class descriptions.
The metadata is therefore split: ✱20·6/61 await CI, while ✱20·59 stays
`prepared`.  The module adds no axiom, description choice operator, `sorry`,
`admit`, or unsafe declaration.

## ✱20·59 v1 object/judgment gate

The v1 gate was re-audited against `FirstEdition/Volume1/Part1/SectionA/Star2.lean`.
That reference architecture has three distinct layers: diplomatic
`PrintedFormula`, a parsed `PM.Elementary` object, and an assertion theorem of
type `PM.Derivation parsed`. The current ✱20·59 declaration supplies none of
the latter two: `star_20_59_target` is only a secondary Lean `Prop` whose
arguments are semantic predicates.

A complete v1 would require object-language constructors for class abstraction
`ẑ(φz)`, contextual class description `(ια)(fα)`, class identity in both
orientations, equivalence, and an assertion/derivation rule respecting PM's
incomplete-symbol discipline. Those constructors and rules do not exist in
the current syntax or `PM.Derivation`; encoding the displayed formula as an
arbitrary elementary atom would erase precisely the class-description content
under audit. No v1 declaration is therefore created, and the item remains
explicitly blocked rather than being promoted on the strength of its `Prop`
shadow.

The dependency graphs were rebuilt from authoritative evidence. The printed
line has no bracketed citation and no demonstration, so its printed and
normalized graphs are empty. The secondary target contains no
`PM.Derivation` call, so its Lean derivation graph is also empty. This empty
graph does not constitute a proof: it records the absence of a derivation,
which is the blocking condition.

## Axiom-free non-v1 Star2/T1–T9 reaudit

The next-wave inventory contains only ✱20·59; no other ✱20 record remains
`prepared`. Reinspection under the stricter Star2/T1–T9 gate does not change
the verdict. `star_20_59_target` is an axiom-free `def` returning a semantic
Lean `Prop`, but it is not an object-language definition printed with `Df` and
is not a proof. It supplies neither the PM AST for class abstraction and
contextual class description, nor an assertion judgement, nor a PM-kernel
derivation. The Prop remains secondary evidence only.

The dependency audit was repeated rather than inherited. The facsimile and
diplomatic source print no citation or demonstration, so the printed graph is
empty. The target body expands only `ClassDescriptionScope` and invokes no
numbered PM theorem or derivation, so the Lean-PM graph is empty. The normalized
graph is therefore empty with strict closure. Target inspection finds no
`axiom`, `sorry`, `admit`, or `unsafe`, but axiom-freedom cannot compensate for
the missing primary layers. The unique item remains blocked and `prepared`.
