# Q361 exact null/universal-class audit

PM I p. 231 / scan leaf 253 is canonical and PG 78050 agrees. No apparatus
or `[sic]` is required for ✱24·102, ·103, ·104, ·105, or ·11.

`Star24Q361Kernel.lean` represents a class extensionally as its membership
predicate. The universal class `V` is the constantly true predicate and the
null class `Λ` the constantly false predicate, exactly as ✱24·01--02 require.
Therefore ✱24·102 and ·103 prove both directions of the printed class
equalities, using function and proposition extensionality only. ✱24·104 and
·105 are their literal membership facts, while ✱24·11 retains universal
quantification over every class and member.

No element type is assumed inhabited and no implication direction is omitted.
The proofs require no `Classical`, choice, new axiom, `sorry`, oracle, or
set-theoretic universe.
