# ✱38 catalogue-01 strict semantic review

Scope: exactly the five items in `PM1-star-38-catalogue-01.json`, checked
against the diplomatic transcription of printed pages 312–313 and against the
declarations in `Star38Kernel.lean`.  The declared formal scope is the typed
reconstruction in which `op : α → β → γ` is a total binary function;
this review does not claim a general model of PM's contextual descriptions.

All five targets are exact within that explicit scope.  ·01 and ·02 identify
the left and right sections extensionally with `y ↦ op x y` and `x ↦ op x y`.
·03 identifies the printed section-image with the image of the right section.
·1 and ·101 retain both sides of the printed biconditionals and merely unfold
the corresponding section at its argument.  No hypothesis, conjunct,
quantifier, equality, or requested case is dropped, and none of the proofs is a
pass-through assumption.

The Lean bodies close by definitional reduction.  Consequently ·1 and ·101
have no direct theorem-constant dependency even though PM cites ·01 and ·02.
Their metadata records this as `relaxed-closure`: the printed citations remain
in the historical graph and no dependency beyond print is introduced.  The
three definitions have empty historical and Lean dependency closures.

Verdict: promote exactly ·01, ·02, ·03, ·1, and ·101 to `awaiting-ci`.
No later ✱38 item was audited or promoted in this review.
