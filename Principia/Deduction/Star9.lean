import Principia.Deduction.System
import Principia.Syntax.CanonicalOrderedFormula

namespace PM.Star9

open PM.CanonicalOrderedFormula

/-- Expand an elementary value into canonical raw syntax before it replaces an
apparent variable.  This is structural recursion in Lean's kernel; it does not
consult the library. -/
def ofElementaryRaw : Elementary Γ → Raw Γ
  | .constant name => .elementary (.constant name)
  | .var entryVar => .elementary (.var entryVar)
  | .neg proposition => .neg (ofElementaryRaw proposition)
  | .disj left right => .disj (ofElementaryRaw left) (ofElementaryRaw right)

/-- Instantiate the apparent variable at `cutoff`, lowering the indices that
cross the removed binder. -/
def instantiateBoundAt (cutoff : Nat) (value : Elementary Γ) : Raw Γ → Raw Γ
  | .elementary proposition => .elementary proposition
  | .schema slot => .schema slot
  | .bound index =>
      if index = cutoff then ofElementaryRaw value
      else if cutoff < index then .bound (index - 1) else .bound index
  | .quantified quantifier body =>
      .quantified quantifier (instantiateBoundAt (cutoff + 1) value body)
  | .neg proposition => .neg (instantiateBoundAt cutoff value proposition)
  | .disj left right =>
      .disj (instantiateBoundAt cutoff value left)
        (instantiateBoundAt cutoff value right)

def instantiateHeadRaw (value : Elementary Γ) (body : Raw Γ) : Raw Γ :=
  instantiateBoundAt 0 value body

/-- Open the apparent variable at `cutoff` as a new leading real variable. -/
def openBoundAt (cutoff : Nat) : Raw Γ → Raw (.elementaryProposition :: Γ)
  | .elementary proposition => .elementary
      (Elementary.schemaInstance (fun entryVar => .var (.succ entryVar)) proposition)
  | .schema slot => .schema slot
  | .bound index =>
      if index = cutoff then .elementary (.var .zero)
      else if cutoff < index then .bound (index - 1) else .bound index
  | .quantified quantifier body =>
      .quantified quantifier (openBoundAt (cutoff + 1) body)
  | .neg proposition => .neg (openBoundAt cutoff proposition)
  | .disj left right =>
      .disj (openBoundAt cutoff left) (openBoundAt cutoff right)

def openHeadRaw (body : Raw Γ) : Raw (.elementaryProposition :: Γ) :=
  openBoundAt 0 body

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

/-! Pure compatibility surface for `Star10`, which is outside this task's
ownership perimeter and historically opened the experimental namespace. -/
namespace PM.Experimental.CanonicalOrderedFormula

export PM.CanonicalOrderedFormula (Raw Quantifier smartNeg smartDisj smartImp)
export PM.Star9 (ofElementaryRaw instantiateBoundAt instantiateHeadRaw openBoundAt openHeadRaw)

end PM.Experimental.CanonicalOrderedFormula
