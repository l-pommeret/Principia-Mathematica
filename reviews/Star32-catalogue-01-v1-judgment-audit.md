# PM I ✱32 catalogue 01 Volume-I judgment audit

The five records are blocked under the Star2 standard. Their declarations live
only in `PM.Architecture` and prove Lean equalities or biconditionals in `Prop`.
No theorem in `PM.FirstEdition.Volume1` constructs a PM object-language formula
and certifies its asserted judgment. Kernel checking these secondary semantic
facts is not a kernel certificate of the printed assertion.

The dependency graphs were rebuilt independently. Printed citations are:

- ·13: ✱32·11 and ✱20·59;
- ·131: ✱32·111 and ✱20·59;
- ·16: ✱32·14 and ✱32·15;
- ·1: ✱21·3 and the defining reference ✱32·01;
- ·101: ✱21·3 and the defining reference ✱32·02.

The actual Lean graph is empty for the four reflexive declarations. For ·16
it contains exactly the calls to `star_32_14` and `star_32_15`, which normalize
to the two printed ✱32 edges. These graphs describe the secondary Prop layer
only and do not cure the absent Volume-I judgment. All five therefore revert
to `prepared` / `blocked-no-v1-object-judgment`; prior CI evidence is not valid
evidence for the stricter target.
