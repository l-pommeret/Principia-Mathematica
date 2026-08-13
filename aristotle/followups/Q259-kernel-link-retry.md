# Q259 strict kernel-link remediation

The previous archive is rejected: it used `Classical` and recreated local
architecture/rulebook declarations instead of linking the canonical targets.

Return only bodies for the four exact interface target signatures supplied in
the context. Use only real, fully-qualified kernel declarations exposed by
that context. Do not define or copy any module, namespace, syntax, deduction
system, rulebook, theorem, helper, `axiom`, `opaque`, or target declaration;
do not use `Classical`, `sorry`, `admit`, or `unsafe`.

If any exact required canonical target or dependency is absent from the
context, stop with an explicit obstruction listing its fully-qualified name
and required signature. Do not simulate it locally.
