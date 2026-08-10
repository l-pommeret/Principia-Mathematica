namespace PM

/-- Skeletal syntax for elementary propositions. Quantification, orders,
ramified types, functions, classes, and relations will be introduced only from
audited source passages. -/
inductive Formula where
  | atom : String → Formula
  | neg : Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

prefix:max "~ₚ" => neg
infixr:55 " ∨ₚ " => disj

/-- Material implication, definitionally expressed using negation and logical
sum. Its status and printed source will be attached during the section ✱1
transcription audit. -/
def imp (p q : Formula) : Formula := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Formula
end PM

