# Q284 — exact Lean integration audit

The canonical first-edition witness is scan leaf 186, printed page 164.  The
five declarations in `Star11Q284Kernel.lean` preserve every displayed binder,
connective, and equivalence of ✱11·46, ✱11·47, ✱11·5, ✱11·51, and ✱11·52.

## Type convention

PM quantifies over the possible arguments of a type.  The reverse directions
of ✱11·46 and ✱11·47 are false for an empty carrier (take `p` false in ✱11·46,
or true in ✱11·47).  Their Lean statements therefore expose this source
convention as `[Nonempty α] [Nonempty β]`; no inhabitant is selected as an
extra mathematical premise.  The three quantifier-negation theorems remain
valid for empty carriers and introduce no such assumptions.

## Dependency audit

The printed demonstrations cite the earlier unary quantifier laws and then
iterate or substitute them.  Lean closes the exact binary endpoints directly
from its logical eliminators plus classical excluded middle.  Consequently no
earlier PM declaration is imported: every printed citation is recorded as a
historical dependency relaxation, and no additional dependency is introduced.

Compilation with the pinned Lean 4.30.0 kernel succeeds.  The file contains no
`axiom`, `sorry`, `admit`, or unsafe escape hatch.
