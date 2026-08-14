# Q281 PM-derivation migration — ✱11·35–·38

All five former canonical declarations are ordinary Lean `Prop` theorems.
They use existential elimination/introduction, function composition, `Iff.trans`,
or conjunction pairing directly. None is stated in an inductive PM judgement,
and none consumes a printed premise through such a judgement. They remain as
secondary `_prop` readings only.

The historical graphs were rebuilt from the source: ✱10·23·271; ✱11·1;
✱11·31/·11/·32; ✱11·31/·11/·33; and ✱11·11/·32. These labels are preserved
as printed, including composites. Since the `_prop` bodies invoke no PM
declaration, every actual Lean and normalized PM graph is empty; nothing is
inherited from the former relaxed closures.

A complete migration requires an inductive derivation relation capable of
lifting and composing the cited rules at a two-apparent-variable endpoint.
Several required ✱11 premises are themselves only targets or secondary Prop
readings after the preceding audits. No structure-support or reflexive reading
can replace that missing relation. Thus all five items are `prepared`, blocked,
and deliberately lack `pm-derivation-v1`.
