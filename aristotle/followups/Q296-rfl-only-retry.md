# Q296 strict reduction-only retry

Return only the exact supplied target declaration and its body. The body must
be `rfl` only. Do not add any import, namespace, declaration, helper, theorem,
axiom, opaque, syntax, local semantic model, or `open scoped Classical`.
In particular, do not mention or define `expand_descriptionScope` or
`DescriptionScopeToy`. If the exact target is not definitional in the provided
context, report that obstruction rather than adding a proof device.
