import Principia.Deduction.System
import Principia.Experimental.CanonicalOrderedFormula

namespace PM.Star9

open PM.Experimental.CanonicalOrderedFormula

/-- The single quantificational deduction judgement of ✱9.

Its constructors are exactly the four primitive propositions printed in
✱9.  Definitions ✱9·01–·08 remain eliminable computations and therefore do
not occur among the constructors. -/
inductive Star9Derivation : {Γ : RealContext} → Raw Γ → Prop where
  /-- ✱9·1: `⊢ : φx .⊃. (∃z).φz`. -/
  | star_9_1 (body : Raw Γ) (value : Elementary Γ) :
      Star9Derivation
        (smartImp (instantiateHeadRaw value body)
          (.quantified .sometimes body))
  /-- ✱9·11: `⊢ : φx ∨ φy .⊃. (∃z).φz`. -/
  | star_9_11 (body : Raw Γ) (x y : Elementary Γ) :
      Star9Derivation
        (smartImp
          (smartDisj (instantiateHeadRaw x body)
            (instantiateHeadRaw y body))
          (.quantified .sometimes body))
  /-- ✱9·12: what is implied by a true premiss is true. -/
  | star_9_12 {premiss conclusion : Raw Γ} :
      Star9Derivation premiss →
      Star9Derivation (smartImp premiss conclusion) →
      Star9Derivation conclusion
  /-- ✱9·13: a real variable in an assertion may be made apparent. -/
  | star_9_13 (body : Raw Γ) :
      Star9Derivation (openHeadRaw body) →
      Star9Derivation (.quantified .always body)

/-- Short name for the isolated ✱9 judgement. -/
abbrev Assertion {Γ : RealContext} (formula : Raw Γ) : Prop :=
  Star9Derivation formula

/-- Catalogue text tied to the exact AST asserted by a primitive instance. -/
structure Reading (Γ : RealContext) where
  printed : String
  parsed : Raw Γ

def star_9_1_reading (body : Raw Γ) (value : Elementary Γ) : Reading Γ where
  printed := "⊢:φx.⊃.(∃z).φz"
  parsed := smartImp (instantiateHeadRaw value body) (.quantified .sometimes body)

def star_9_11_reading (body : Raw Γ) (x y : Elementary Γ) : Reading Γ where
  printed := "⊢:φx∨φy.⊃.(∃z).φz"
  parsed := smartImp (smartDisj (instantiateHeadRaw x body)
    (instantiateHeadRaw y body)) (.quantified .sometimes body)

theorem star_9_1 (body : Raw Γ) (value : Elementary Γ) :
    Assertion (star_9_1_reading body value).parsed :=
  Star9Derivation.star_9_1 body value

theorem star_9_11 (body : Raw Γ) (x y : Elementary Γ) :
    Assertion (star_9_11_reading body x y).parsed :=
  Star9Derivation.star_9_11 body x y

end PM.Star9
