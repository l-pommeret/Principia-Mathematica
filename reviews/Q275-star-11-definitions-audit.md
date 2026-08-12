# Q275 ✱11 definitions audit

All five records are definitions, not assertion principles. The existing
typed apparent-variable syntax already supports their exact arities: two or
three successive `Quantified` constructors preserve binder order, and ✱11·05
places the matrix implication below precisely the two binders of ✱11·01.
No function semantics, significance predicate, assertion constructor, axiom,
or order-polymorphic quantifier was added.

Promotion simulation passes all five declarations with exact empty
`lean_dependencies` and `normalized_dependencies`. Their bodies use only the
typed syntax constructors that constitute the definitions themselves; the
source prints no prior proof dependencies. No relaxation is required and no
status is promoted by this audit.
