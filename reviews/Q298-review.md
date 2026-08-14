# Q298 review — exact contextual targets, assertion layer still blocked

Leaf 205 (p. 183), SHA-256
`1a8f4bf7870135c6f7047f5f5b6a6ac1fe416f327c28b59766fce3711c3e1a7c`,
and PG 78050 collate ✱14·202/204/205/28/13.  The metadata now preserves
the full four-member chain at ✱14·202; the former shortened text omitted its
two reversed-identity members.

`Principia/Architecture/Star14Q298Targets.lean` supplies exact intrinsically
typed targets for all five loci.  Every description occurrence is eliminated
by `Formula.descriptionScope`.  In particular:

- neither side of a displayed identity receives a `Term.description`;
- the existential witness in ✱14·204/205 is an apparent de Bruijn variable;
- the condition and continuation cross that witness capture-free;
- the one scope in ✱14·28 binds both occurrences of the same incomplete symbol;
- ✱14·202 is exposed as its four ordered formula members rather than flattened
  into an invented Lean equality.

Lean 4.30.0 accepts the target module.  This resolves the earlier
“incomplete-symbol syntax” part of the blocker, but it proves none of the five
assertions.  The remaining missing component is still a source-licensed
`DescriptionDerivation (formula : Formula …) : Prop` calculus with contextual
identity, existential, equivalence, and substitution rules.  Consequently all
five metadata records remain `prepared`; no CI or kernel-checked status is
claimed, and the target module introduces no axiom, assertion constructor,
semantic interpretation, `sorry`, or `admit`.

## Star2-standard v1 reaudit

The five records were reaudited from zero under the Star2 standard: an exact
object AST, an assertion judgement over that AST, and a PM-kernel derivation
inhabiting the judgement are three distinct primary layers. A Lean `Prop`
theorem would be secondary evidence and could not replace the latter layers.

Q298 supplies the exact AST layer only. Its public declarations are `def`
targets returning `Formula` (or, for ·202, a structure of four `Formula`s).
There is no judgement indexed by those formulas, no derivation object, and no
theorem proving any of the five printed assertions. All five therefore remain
blocked in v1 and `prepared`; exact syntax alone is not called complete.

The three dependency graphs were independently reconstructed from the actual
demonstrations, rather than inferred only from the diplomatic proposition
lines.  The printed graph is:

- ✱14·202: ✱14·1, ✱13·195;
- ✱14·204: ✱14·202, ✱10·11, ✱10·281, ✱14·11;
- ✱14·205: ✱14·202, ✱14·1 (the compact bracket `✱14·202·1`);
- ✱14·28: ✱13·15, ✱4·73, ✱10·11, ✱10·281, ✱14·1, ✱14·11;
- ✱14·13: ✱14·1, ✱13·16, ✱4·36, ✱10·11, ✱10·281.

Compact same-star citations such as `✱10·11·281` and `✱14·1·11` are
split into the two exact catalogue identifiers, never recorded as a synthetic
compound identifier.

The Lean PM graph remains empty because the definitions call only
formula/description syntax and capture-safe substitutions, never a PM theorem
or derivation. The normalized PM graph is consequently empty. This faithfully
records the gap between the historical proof and an AST-only target; it does
not repair the missing judgement and derivation.
