# ✱55 catalogues 05–06 strict semantic audit

The ten loci were audited in two groups of five against their typed Lean
declarations. Catalogue 05 has three exact reconstructions: ·224 is the
singleton intersection of the left/right pair families, and ·23/·231 are the
two exact image characterizations. Items ·222 and ·223 are refused because
Lean adds `hu : ∃ a b, R = pair a b`; PM's displayed biconditionals do not
assume in advance that the arbitrary relation is an ordinal couple.

Catalogue 06 has four exact typed reconstructions. Item ·232 preserves the
unique-existence equivalence, ·24 and ·241 give the two singleton-cross-product
image classes extensionally, and ·25 gives the unique singleton domain-image
class. Item ·233 is refused: PM concludes equality of the intersection class
with the empty class, while Lean proves only failure of `HasUnique`; that is
not the printed extensional conclusion.

Eligible items must be split into homogeneous `awaiting-ci` manifests and the
three refusals into homogeneous `prepared`/`blocked-semantic-mismatch`
manifests before integration. Compilation does not upgrade any status.
