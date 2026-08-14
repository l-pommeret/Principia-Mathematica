# ✱33 catalogue 01 strict semantic audit

Scope: exactly the five items ✱33·2, ·3, ·4, ·5, and ·6, compared with their
verbatim transcriptions and the declarations in `Star33DomainKernel2.lean`,
`Star33DomainKernel4.lean`, `Star33DomainKernel5.lean`, and
`Star33DomainKernel6.lean`.

All five pass strict equivalence only in the catalogue's secondary typed
`Prop` reconstruction.
✱33·2 identifies converse-domain with the domain of converse. ✱33·3 retains
both directions between inclusion in the domain and pointwise existence of a
second correlate. ✱33·4 is the corresponding extensional domain identity;
PM's contextual existence notation is represented by inhabitation of the
section, not by a uniqueness claim. ✱33·5 identifies the field-valued operator
with the forward relation of field membership, extensionally at relation and
object arguments. ✱33·6 unfolds the converse fibre of the domain operator to
equality with the domain.

No printed citation occurs in this lot, and inspection of the five declaration
bodies finds no call to a numbered PM theorem. Thus the rebuilt printed, Lean,
and normalized dependency graphs are all empty.

## Structural v1 gate

Under the ✱2 standard, the `Prop` theorems above are secondary projections,
not the primary proof artifact. A complete v1 item must expose:

1. a typed PM AST retaining domain, converse-domain, converse relation,
   inclusion, contextual existence, field, and inverse-fibre structure;
2. the corresponding well-formed assertion judgement; and
3. a kernel-checked derivation of that judgement.

None of the four ✱33 kernel files supplies those artifacts. The shared
`PM.Elementary` syntax currently has only propositional constants, variables,
negation, and disjunction. Encoding each full relational formula as one opaque
constant would erase precisely the AST structure required here, while
postulating a derivation of that atom would add an unlicensed axiom. Therefore
all five items are **blocked in v1** with
`blocked-missing-pm-ast-judgement-derivation`. Their correct secondary `Prop`
statements remain useful, but none is eligible for `awaiting-ci` or complete
source-critical coverage until the typed relational syntax and derivations
exist.
