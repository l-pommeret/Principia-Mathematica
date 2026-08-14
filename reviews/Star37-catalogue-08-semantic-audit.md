# ✱37 catalogue-08 strict PM-kernel audit

This audit covers exactly five items: ✱37·14, ·17, ·171, ·18, and ·181. The
acceptance standard is the one used for ✱2: an object-language `Formula` AST,
a PM judgement, and a kernel-checked derivation of that judgement. A semantic
`Prop` theorem may be retained only as a secondary corollary and cannot replace
the primary derivation.

All five records are source-only. Their `lean_path` is the diplomatic
`Star37Source.lean`, their declaration field explicitly says that no Lean
declaration exists, and targeted lookup finds no corresponding `star_37_14`,
`star_37_17`, `star_37_171`, `star_37_18`, or `star_37_181`. Thus none has a
formula AST, judgement, proof term, or even a secondary Prop theorem. Every
item is blocked in v1 as `blocked-no-pm-derivation`; no neighbouring typed-set
lemma is substituted for the missing object-language proof.

## Dependency graphs rebuilt from zero

- ✱37·14, ·17, ·171, and ·18 print no numbered predecessor, contain no Lean
  declaration, and therefore have empty printed, Lean, and normalized graphs.
- ✱37·181 explicitly prints “Proof as in ✱37·18”, giving one historical edge
  to `PM1:✱37·18`. With no Lean declaration its real Lean graph is empty, and
  hence its normalized graph is empty. An explicit `relaxed-closure` record
  preserves the printed-but-unused edge without fabricating a proof call.

The five identifiers are unique, the lot remains within the maximum size, and
no `awaiting-ci` sidecar is created because no complete v1 artifact exists.
