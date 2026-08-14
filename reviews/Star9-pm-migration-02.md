# ✱9 PM migration — lot 02

The next five `axiom-free` report entries not already migrated are ✱9·32, ✱9·01, ✱9·011, ✱9·02, and ✱9·021.

## Definitions

The four `Df` entries are syntax definitions, not assertion constructors. Their level is `pm-definition-v1`, never `pm-derivation-v1`. ✱9·01 and ✱9·02 directly build their printed `FirstOrder` definiens. ✱9·011 and ✱9·021 are reducible brace-omission aliases that unfold through ✱9·01 and ✱9·02 respectively. Their certificates are kernel definitional reduction; no `Support`, axiom, or derivation constructor is credited to them.

Their rebuilt graphs are therefore empty for ✱9·01 and ✱9·02, and the single definitional edge ✱9·011 → ✱9·01 / ✱9·021 → ✱9·02 for the aliases.

## Refusal: ✱9·32

The target is a genuine `OrderedAssertion` and its body uses the real `PM.Derivation.star_1_3`, `OrderedAssertion.star_9_13`, and `OrderedAssertion.star_9_12` steps. However, the printed ✱9·25 stage is obtained from the parameter `Q259ClosedRuleBook.star_9_25`. That field is external support, not a theorem proved by the certificate. Consequently ✱9·32 remains `prepared` and explicitly blocked from `pm-derivation-v1`, despite the current declaration being axiom-free after abstracting over that support.
