import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.CanonicalNormalization

open PM.CanonicalOrderedFormula

/-- Source-labelled scope normalizations for the printed ✱9 definition chain.
This is syntax evidence only: it introduces no assertion or derivation. -/
inductive NormalizesScoped : Raw Γ → Raw Γ → Prop where
  | refl (p) : NormalizesScoped p p
  | negAlways (p) :
      NormalizesScoped (.neg (.quantified .always p))
        (.quantified .sometimes (.neg p))
  | negSometimes (p) :
      NormalizesScoped (.neg (.quantified .sometimes p))
        (.quantified .always (.neg p))
  | disjRight (q p r) :
      NormalizesScoped (.disj (.quantified q p) r)
        (.quantified q (.disj p (weakenBound r)))
  | disjLeft (q p r) :
      NormalizesScoped (.disj r (.quantified q p))
        (.quantified q (.disj (weakenBound r) p))
  /-- ✱9·07: universal-left/existential-right, retaining `x` outside `y`. -/
  | disjAlwaysSometimes (p q) :
      NormalizesScoped (.disj (.quantified .always p) (.quantified .sometimes q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound p) q)))
  /-- ✱9·08: existential-left/universal-right, with the same printed binder
order after the scope normalization. -/
  | disjSometimesAlways (p q) :
      NormalizesScoped (.disj (.quantified .sometimes p) (.quantified .always q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound q) p)))

end PM.Architecture.CanonicalNormalization
