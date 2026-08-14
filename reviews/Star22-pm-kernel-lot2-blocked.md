# ✱22 syntax-first audit, lot 2: blocked

Targets: ✱22·33, ·34, ·35, ·351, and ·36.

No target is counted as a PM derivation. The printed graphs are:

- ✱22·33: ✱20·3 and ✱22·2;
- ✱22·34: ✱20·3 and ✱22·3;
- ✱22·35: ✱20·3 and ✱22·31;
- ✱22·351: ✱22·35, ✱5·19, ✱10·11, ✱10·251, and ✱20·43;
- ✱22·36: ✱20·41.

The repository has secondary Lean-`Prop` theorems for these statements, but
none of the cited ✱20 nodes is currently exported as a derivation over a PM
class-formula AST. Consequently there is no typed citation that a ✱22
derivation can consume. Adding constructors bearing those citation names would
be precisely the forbidden `Support` anti-pattern.

The chapter nevertheless advances structurally. `Principia.Syntax.Class`
now owns the actual class-term/formula AST and assertion endpoint. ✱22·01–05
are eliminable `def`s, with difference genuinely unfolding to intersection
with complement. `Star22PMInfrastructure` exposes only checked unfolding
equalities; it defines no derivation constructor and claims no migrated proof.
This lot remains blocked until the cited ✱20 derivations exist.
