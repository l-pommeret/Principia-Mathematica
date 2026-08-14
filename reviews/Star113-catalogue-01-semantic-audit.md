# PM II ✱113 catalogue-01 strict semantic audit

This audit is limited to the first five implemented namesakes in the opening
kernel: ✱113·1, ·101, ·102, ·104, and ·105.  Their displayed formulas
were checked against the first edition, volume II, printed pp. 108–109 (scan
leaves 148–149), with Project Gutenberg 78255 as a searchable control witness.
The comparison is by theorem type and represented operations, not by shared
number or an informal mathematical consequence.

Two items pass and are marked `awaiting-ci`:

- ✱113·101 gives exactly the typed membership characterization of the class
  product: its members are precisely ordered-pair relations whose first
  coordinate belongs to alpha and second coordinate belongs to beta.
- ✱113·104 asserts existence of the fixed-second-coordinate fibre class.
  Lean's predicate representation constructs exactly that class; no choice of
  an arbitrary representative or extra mathematical hypothesis is introduced.

Three items are refused and remain `prepared`:

- ✱113·1 identifies the product with the union of an indexed family of
  fibres.  Lean instead unfolds `Product` straight to the existential
  ordered-pair formula later printed as ✱113·101.  The image and union layers
  of ·1 are absent, so equivalence after an unformalized bridge is insufficient.
- ✱113·102 identifies a fibre with a selection/image construction under
  `y∈β`.  Its Lean namesake is a reflexive equality of the direct
  comprehension, does not represent the selection/image side, and never uses
  the beta-membership hypothesis.
- ✱113·105 says that, when alpha exists, the function sending the varying
  second coordinate `y` to the alpha-fibre at `y` is one-to-one.  Lean instead
  fixes `z` and proves injectivity in the first coordinate among alpha's
  members.  This is a different map, and the printed `1→1` assertion is absent.

The exact and refused records are separated so that only the two exact items
can enter an awaiting-CI integration wave.  Printed proof dependencies remain
historical graph data; both accepted Lean declarations close definitionally,
so their unused printed routes are recorded as relaxed closures.
