# ✱207 partial source catalogue review

The 45 existing `PM-VERBATIM` blocks in `Star207Source.lean` are catalogued in nine batches of at most five items. The witnesses are Project Gutenberg 78255 and the 1912 Volume II facsimile, printed pages 596–603. This catalogue is limited to the blocks already transcribed and makes no completeness claim for the whole section.

Every item has a homonymous declaration in one of the three `Star207*Kernel.lean` files. These declarations remain `prepared`: many are abstract restatements or consequences of supplied hypotheses. No entry is promoted by this catalogue.

The first batch (·01, ·02, ·03, ·04, ·121) has now received an item-level
semantic audit. None is exact. The ·01 declaration omits the printed second
definitional equality `lt(P)`; ·02 additionally represents `tl` by the same
`Lt` construction; ·03 replaces the printed relational construction by a
pointwise predicate union; ·04 reuses `Limax` rather than defining `limin`;
and ·121 merely assumes an arbitrary equality, omitting the printed
antecedent and order-theoretic operators. These five are classified
`architecture-blocked` in the pipeline and remain `prepared`.

The deterministic PM parser does not yet cover the order-theoretic relation, restriction, converse-image, class-description, and ancestral notation used here. All 45 items therefore use the explicit `reviewed-gap` route pending semantic audit.
