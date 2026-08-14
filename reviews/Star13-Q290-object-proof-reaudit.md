# ✱13 Q290 object-proof re-audit

Scope: exactly ✱13·01, ·02, ·03, ·1, and ·101. This re-audit applies the
Star2/T1–T9 standard: definitions are syntax/normalization data and never
assertion constructors; derived propositions require a real PM object
judgement and derivation. An ordinary Lean `Prop` theorem is secondary and
cannot establish `pm-derivation-v1`.

None of the five current declarations meets that completion gate.

- ✱13·01, ·02, and ·03 are `Df` loci. Their current declarations are semantic
  `Prop` definitions or abbreviations. Creating primitive derivation
  constructors for them would falsely turn definitions into asserted
  propositions. The experimental predicative AST contains a useful ·01
  definiens shape, but it is not a canonical T1–T9 definition-normalization
  certificate; ·02 and ·03 have no corresponding PM AST integration.
- ✱13·1 is proved by Lean reflexivity after unfolding the semantic
  `star_13_01`. It does not inhabit a PM judgement and does not reconstruct
  the printed use of ✱4·2, ✱13·01, and ✱10·02.
- ✱13·101 is a valid secondary semantic theorem, but it assumes a
  `Reducibility` model interface and reasons directly in `Prop`. It neither
  consumes the new ✱12·1 PM derivation certificate nor reconstructs the
  printed ✱13·1, ✱4·84, ✱4·85, ✱10·27, and ✱10·23 chain.

No axiom, theorem-specific oracle, fake citation constructor, or Df constructor
is added. All five items remain `prepared` and explicitly blocked; none is
labelled `pm-derivation-v1`.

The three graphs were rebuilt from the source and current Lean bodies, with no
inherited relaxation record. The printed graph is empty for the three Df loci;
·1 records ✱4·2, ✱13·01, and ✱10·02; ·101 records ✱12·1, ✱13·1, ✱4·84,
✱4·85, ✱10·27, and ✱10·23 as six distinct citations. The normalized graph
records only actual use of the identity definition. The Lean graph records
only the constants called by the semantic implementation, including the
`Reducibility.reducibility` projection for ·101. Prior green CI covered the
weaker semantic layer and is reset to pending.

