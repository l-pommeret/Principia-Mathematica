/- Architecture-experimental opaque interface. This file is not a repository import,
   does not establish canonical PM coverage, and cannot be promoted. -/

import Principia.Syntax.Apparent

-- OPAQUE-PM-DEPENDENCY PM1:✱9·03 4a93ebde8b2739c4df14f6bca9d50ff02b1eed5f2b48c2824d113d5b55872e00
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_03 {Γ Δ}
    (body : PM.Apparent Γ (.elementaryProposition :: Δ))
    (proposition : PM.Elementary Γ) : PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·04 3e70e4d0a88f30428a666afffd907f0c5df6d7da75594d3fe7e69cb0628ae6a6
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_04 {Γ Δ}
    (proposition : PM.Elementary Γ)
    (body : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·05 b7886cd8227a0f21f0564e5586112b13ea0bd0106aa61547a218440e0b12d97c
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_05 {Γ Δ}
    (body : PM.Apparent Γ (.elementaryProposition :: Δ))
    (proposition : PM.Elementary Γ) : PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9

-- OPAQUE-PM-DEPENDENCY PM1:✱9·06 49af3daa13583aa728671180ffe5283c557de4648c8a80ebc1fb1a19ffb4c380
namespace PM.FirstEdition.Volume1.Star9

axiom star_9_06 {Γ Δ}
    (proposition : PM.Elementary Γ)
    (body : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ

end PM.FirstEdition.Volume1.Star9
