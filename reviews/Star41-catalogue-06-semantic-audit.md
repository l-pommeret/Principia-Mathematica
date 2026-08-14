# ✱41 catalogue 06 strict semantic audit

The five statements ✱41·27 and ✱41·3–33 were checked against the typed
relation-class model in `Star41ConverseKernel.lean`. The encodings of relational
intersection, empty relation, converse, pointwise image of a relation class,
and the lifted product/sum value classes are explicit and nondegenerate.

✱41·27 preserves both directions of the printed disjointness law. ✱41·3 and
✱41·31 prove the product and sum converse laws pointwise. ✱41·32 and
✱41·33 lift precisely those laws to classes of relation classes, reusing the
corresponding checked base theorem. No declaration assumes its conclusion or
narrows the source quantification. All five are therefore `awaiting-ci`.
