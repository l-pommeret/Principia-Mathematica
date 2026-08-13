# ✱205 partial source catalogue review

Project Gutenberg 78255 and the 1912 Volume II facsimile show 107 numbered
items in ✱205 (definition ·01 plus 106 displayed propositions), on printed
pages 559–577. The diplomatic source now contains all 107 of them, in printed
order. The catalogue does not infer missing formal targets from similarly
named Lean declarations.

Eighty-two transcribed IDs have a homonymous Lean declaration. They remain
`prepared` because the large typed reconstruction contains many abstract
corollaries and restated hypotheses whose item-level equivalence to PM has not
been established. The apparent declarations `star_205_33b` and `star_205_68b`
do not match the printed targets ·33 and ·68, so those two loci remain
source-only rather than being renamed cosmetically. The newly transcribed
·252–·256, ·262, ·36–·38, ·381, ·401–·44, and ·501 likewise remain
source-only where the kernel has no homonymous declaration for them.
Among the ·54–·71 tranche, ·65 also remains source-only; all other loci in
that tranche have only a nominal mapping pending semantic audit.
The closing ·72–·91 tranche leaves ·9, ·732, ·742, ·832, and ·833 source-only;
the remaining loci in that tranche are nominal mappings only.

The PM parser does not support the minimum/maximum relation operators and the
associated restriction, converse-image, ancestral, and descriptive notation;
all entries therefore carry `reviewed-gap`. The source catalogue is complete,
but this is not a claim that ✱205 is formally or semantically proved.

Targeted audit exception: ✱205·15, ·16, ·161, ·181, ·182, ·21 and ·195 have
faithful typed endpoints in `Star205OpeningKernel.lean`; their unique canonical
records are `awaiting-ci`. No promotion is implied for any other ✱205 item.
