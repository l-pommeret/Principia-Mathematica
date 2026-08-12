# Q346 review — PM I ✱22·33–36

PM I p. 220 / scan leaf 242 and PG 78050 agree on the five statements and
their citations.  `Star22Q346Kernel.lean` proves every complete endpoint over
the explicitly typed extensional class carrier introduced at ✱22·01–05.

✱22·33/34/35 are definitional membership reductions for intersection, union,
and complement.  ✱22·351 is genuinely conditional on the element type being
nonempty: on an empty type its unique class equals its complement.  The Lean
signature exposes `[Nonempty Object]`, exactly the repository-wide reading of
PM's “possible argument” convention, and proves inequality by inspecting one
argument.  ✱22·36 uses characteristic functions themselves as the explicit
predicative codes in the type-relative `Cls`; the intersection function is its
own witness.

The historical dependency chains remain recorded, while the proofs close the
same endpoints directly from the already integrated typed definitions.  No
untyped universal class, choice of a class description, reducibility axiom,
`sorry`, `admit`, or unsafe declaration is introduced.  All five items are
therefore eligible for `awaiting-ci`.
