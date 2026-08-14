# ✱37 catalogue-03 semantic audit

This strict item-level audit covers at most five formulas.  Three declarations
match their printed claims exactly and are promoted to `awaiting-ci`.

- ✱37·22 defines relational image with PM's output-first orientation and proves
  equality of predicates in both directions, so it is exactly distribution of
  image over class union.
- ✱37·25 proves both displayed equalities.  `domain R` is the class of first
  arguments, `converseDomain R` the class of second arguments, and `converse`
  reverses the arguments; neither conjunct is omitted or weakened.
- ✱37·26 proves equality in both directions after restricting the input class
  to the converse-domain.  The witness used to establish converse-domain
  membership is the same related pair already present in the image.

✱37·15 and ·16 are refused for promotion.  They exist only as diplomatic
`PM-VERBATIM` source blocks in `Star37Source.lean`; there is no Lean declaration,
target, or proof whose semantics could be checked.  Their refusal is recorded
separately in `PM1-star-37-catalogue-03-refused.json`, and no substitute theorem
is inferred from the neighbouring architecture files.
