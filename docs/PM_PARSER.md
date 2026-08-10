# Deterministic Peano–Russell syntax parser

`scripts/pm_syntax.py` parses printed formulae into a serializable object AST.
It is an editorial compiler front end, not a semantic interpretation of PM.

The currently audited grammar covers:

- the propositional dot/colon scope system and assertion sign;
- universal and existential apparent-variable binders;
- definition signs as definitions rather than equality propositions;
- left-associated unmarked disjunction/product and right-associated implication;
- general applications `φx` and structurally distinct predicative applications
  `φ!x`, including multiple arguments;
- object equality, membership, and indexed formal equivalence such as `≡ₓ`;
- contextual descriptions with explicit printed scope.

The discriminating source tests include the exact shapes of ✱12·1, ✱13·01,
and ✱14·01. In the resulting ✱14 AST, a description is never retained as a
term supplied to a function. `description_scope` owns the defining condition,
and matching surface occurrences in its continuation become
`description_bound`. Narrow and wide scope therefore produce different trees
without postulating a denoting description object.

This is still a syntactic AST, not yet the intrinsically typed Lean AST of the
canonical ramified calculus. Class abstractions, relation expressions,
relative products, higher-order function variables, and systematic ambiguity
remain explicit future grammar gates. Until those are implemented and tested
against their source loci, parser success must not be claimed for those
sections.
