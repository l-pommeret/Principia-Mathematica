# ✱33 catalogue 02 strict semantic audit

The five literal source blocks PM1:✱33·13, ·14, ·15, ·16, and ·17 were
compared with their catalogue records and with the corresponding declarations
in `Star33DomainKernel.lean` and `Star33DomainKernel2.lean`. The reconstruction
interprets PM's domain, converse domain, field, section, class inclusion, and
class union by their direct typed predicates.

All five translations pass strict equivalence. Proposition ·13 unfolds domain
membership into existence of a second correlate; ·14 places the two correlates
of a relation instance in its domain and converse domain; ·15 includes a
fixed-second-coordinate section in the domain; ·16 identifies the field with
the union of domain and converse domain; and ·17 places both correlates in the
field. No item is refused.

The printed dependency graph records ·13's citations to ✱33·11, ✱20·3, and
✱20·57, and ·17's citations to ✱33·14 and ✱33·161. The secondary Lean
declarations prove the same endpoints directly from local definitions and
hypotheses, so their bodies contain no numbered PM theorem call. Their Lean
and normalized graphs are empty; the five printed citations remain explicit
printed-but-unused historical relaxations rather than inherited graph edges.

## Structural v1 gate: blocked

Under the ✱2 and T1–T9 standard, all five items fail the primary artifact gate.
The files define relation operations as ordinary Lean functions and prove
ordinary `Prop` statements. They do not construct a typed PM relational AST,
a well-formed PM assertion judgement, or a kernel derivation of that
judgement. Thus the correct `Prop` theorems are secondary only.

The missing structure is material: ·13 must retain domain membership,
existential binding, and relation application as object syntax; ·14 must retain
implication and both membership conclusions; ·15 must retain class inclusion;
·16 must retain field, domain, converse-domain, union, and equality; and ·17
must retain implication and joint field membership. Encoding any full formula
as an opaque propositional atom would erase this structure, while postulating
its derivation would violate the axiom-free requirement.

Accordingly the five items are `prepared` and
`blocked-missing-pm-ast-judgement-derivation`. Their previously successful CI
record is preserved as evidence that the secondary Prop layer compiled, not
as v1 completion evidence. No item is eligible for primary promotion until a
complete axiom-free object formula and judgement proof exists and the printed
rules are genuinely consumed where cited.
