# Kernel promotion audit — PM I ✱4·1, ·11, ·12, ·13

The four declarations were compiled and kernel-checked by Lean CI run
[`31542913579`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31542913579)
at commit `be26037f8ccd8d283ab35657d4d810809b65dcb9`.  The run checked the
canonical `Star4.lean` module, not an Aristotle-local copy or interface stub.

The printed citations do not spell out every metalinguistic packaging step.
The dependency closures recorded in the promoted metadata are extracted from
the accepted Lean bodies.  In particular, `PM.Derivation.detach` selects
✱1·1 for closed formulas and ✱1·11 for nonempty real-variable contexts;
✱3·2 packages two implication directions as a conjunction; ✱3·47 transports
paired implications; and ✱2·05 composes the component permutation in ✱4·11.
These additions are recorded as historical dependency relaxations rather than
silently attributed to the printed brackets.

The sibling definitions ✱4·01/·02 and propositions ✱4·14/·15/·2 remain in
their original prepared batches.  This re-segmentation changes no PM identity,
source reading, Lean declaration, or proof body.
