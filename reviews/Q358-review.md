# Q358 exact Boolean-class audit

The five endpoints on PM I p. 224, scan leaf 246, are formalized completely in
`Star22Q358Kernel.lean` under the explicit class-extension interpretation
`α → Prop`. Union, intersection, and difference are their printed pointwise
definitions; equality is established by function and proposition
extensionality rather than postulated.

✱22·89, ✱22·9, and ✱22·93 are constructive. ✱22·91 and ✱22·92 use a local
case split on membership in `α`, exactly the classical Boolean step needed by
the printed decomposition. No global classical instance, decidable equality,
inhabitance assumption, new axiom, placeholder, or unsafe declaration occurs.

PM I p. 224 / leaf 246 is canonical; PG 78050 agrees. No apparatus or `[sic]` is required.
