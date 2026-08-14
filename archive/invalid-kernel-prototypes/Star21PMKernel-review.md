# ✱21 syntax-first PM-kernel audit, v1

## Integration correction

This module is an AST/derivation skeleton, not yet certifiable as
`pm-derivation-v1`: its `Support` constructors represent earlier printed nodes
but do not consume the actual kernel derivations of those nodes. They would
therefore turn historical citations into fresh primitive assumptions. The
five existing metadata records remain subject to the strict gate and must not
be redirected to this module until typed cross-fragment bridges replace
`Support`.

Scope: the first five derived propositions ✱21·1, ·11, ·111, ·112, and
·12. The definitions ✱21·01–03 and ·07–083 remain syntactic support and are
not counted as migrated proofs.

`Star21PMKernel.lean` makes the PM object language primary: relation abstracts,
predicative relation variables, functional application, equivalence,
implication, conjunction, and existential binding are nodes of an inductive
AST. `Judgement.asserted` is separate from Lean's semantic `Prop`, and each
exported theorem constructs an indexed `Derivation` of its exact parsed AST.
The pre-existing function/set `Prop` theorems are deliberately not called.

The kernel-visible proof graph reproduces every printed edge:

- ✱21·1 calls ✱4·2 and definition ✱21·01;
- ✱21·11 calls ✱4·86·36, ✱10·281, and the migrated ✱21·1 certificate;
- ✱21·111 calls `Fact`, ✱11·11·3, ✱10·281, and the migrated ✱21·1
  certificate. These citations come from the full first-edition/Gutenberg
  demonstration line and repair their omission from the former summary
  metadata;
- ✱21·112 calls ✱12·1 and the migrated ✱21·111 certificate;
- ✱21·12 calls the migrated ✱21·11 certificate and ✱12·11.

All downstream ✱21 calls are actual Lean arguments of the corresponding
derivation constructor. Thus no classical truth proof, extensionality theorem,
or self-witness substitutes for a historical PM edge. The v1 scope is complete
for these five proofs; later propositions are outside this audit.
