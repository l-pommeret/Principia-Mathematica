import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

theorem natMaxCongr
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order) :
    max leftOrder rightOrder = order := by
  cases leftEq
  cases rightEq
  exact natMaxSelf _

/-- An actually heterogeneous disjunction reduces to the established
same-order abbreviation when both of its members are proved to have the
common order. -/
theorem Formula.disj_normalizeSameOrder
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order)
    (disjunction : signature.Disjunction order)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    let resultEq := natMaxCongr leftEq rightEq
    Eq.mp (congrArg (Formula signature real apparent) resultEq)
        (.disj
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          left right) =
      sameDisjunction disjunction
        (Eq.mp (congrArg (Formula signature real apparent) leftEq) left)
        (Eq.mp (congrArg (Formula signature real apparent) rightEq) right) := by
  cases leftEq
  cases rightEq
  rfl

/-- An actually heterogeneous implication reduces to the established
same-order abbreviation when both of its members are proved to have the
common order. -/
theorem mixedImplication_normalizeSameOrder
    {leftOrder rightOrder order : Nat}
    (leftEq : leftOrder = order)
    (rightEq : rightOrder = order)
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (left : Formula signature real apparent leftOrder)
    (right : Formula signature real apparent rightOrder) :
    let resultEq := natMaxCongr leftEq rightEq
    Eq.mp (congrArg (Formula signature real apparent) resultEq)
        (mixedImplication
          (Eq.mp (congrArg signature.Negation leftEq.symm) negation)
          (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
          left right) =
      implication negation disjunction
        (Eq.mp (congrArg (Formula signature real apparent) leftEq) left)
        (Eq.mp (congrArg (Formula signature real apparent) rightEq) right) := by
  cases leftEq
  cases rightEq
  rfl

theorem maxSelfRightNested (order : Nat) :
    max order (max order order) = order :=
  natMaxCongr rfl (natMaxSelf order)

def rawStar13
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Formula signature real [] (max order (max order order)) :=
  mixedImplication negation
    (Eq.mp (congrArg signature.Disjunction
      (maxSelfRightNested order).symm) disjunction)
    q
    (.disj
      (Eq.mp (congrArg signature.Disjunction
        (natMaxSelf order).symm) disjunction)
      p q)

theorem rawStar13_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Eq.mp (congrArg (Formula signature real []) (maxSelfRightNested order))
        (rawStar13 negation disjunction p q) =
      implication negation disjunction q (sameDisjunction disjunction p q) := by
  exact mixedImplication_normalizeSameOrder rfl (natMaxSelf order)
    negation disjunction q
    (.disj
      (Eq.mp (congrArg signature.Disjunction
        (natMaxSelf order).symm) disjunction)
      p q)

def rawStar14
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    Formula signature real []
      (max (max order order) (max order order)) :=
  let pairEq := natMaxSelf order
  let resultEq := natMaxCongr pairEq pairEq
  mixedImplication
    (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
    (.disj
      (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q)
    (.disj
      (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q p)

theorem rawStar14_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let resultEq := natMaxCongr pairEq pairEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (rawStar14 negation disjunction p q) =
      implication negation disjunction
        (sameDisjunction disjunction p q)
        (sameDisjunction disjunction q p) := by
  let pairEq := natMaxSelf order
  let left := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q
  let right := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q p
  exact Eq.trans
    (mixedImplication_normalizeSameOrder pairEq pairEq
      negation disjunction left right)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) pairEq) right))
        (Formula.disj_normalizeSameOrder rfl rfl disjunction p q))
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p q))
        (Formula.disj_normalizeSameOrder rfl rfl disjunction q p)))

def rawStar15
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Formula signature real []
      (max (max order (max order order))
        (max order (max order order))) :=
  let pairEq := natMaxSelf order
  let nestedEq := natMaxCongr rfl pairEq
  let resultEq := natMaxCongr nestedEq nestedEq
  mixedImplication
    (Eq.mp (congrArg signature.Negation nestedEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
    (.disj
      (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction)
      p
      (.disj
        (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
        q r))
    (.disj
      (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction)
      q
      (.disj
        (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction)
        p r))

theorem rawStar15_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let nestedEq := natMaxCongr rfl pairEq
    let resultEq := natMaxCongr nestedEq nestedEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (rawStar15 negation disjunction p q r) =
      implication negation disjunction
        (sameDisjunction disjunction p (sameDisjunction disjunction q r))
        (sameDisjunction disjunction q (sameDisjunction disjunction p r)) := by
  let pairEq := natMaxSelf order
  let nestedEq := natMaxCongr rfl pairEq
  let qr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q r
  let pr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p r
  let left := Formula.disj
    (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction) p qr
  let right := Formula.disj
    (Eq.mp (congrArg signature.Disjunction nestedEq.symm) disjunction) q pr
  have qrEq := Formula.disj_normalizeSameOrder rfl rfl disjunction q r
  have prEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p r
  have leftStep := Formula.disj_normalizeSameOrder rfl pairEq disjunction p qr
  have rightStep := Formula.disj_normalizeSameOrder rfl pairEq disjunction q pr
  have leftEq := Eq.trans leftStep
    (congrArg (sameDisjunction disjunction p) qrEq)
  have rightEq := Eq.trans rightStep
    (congrArg (sameDisjunction disjunction q) prEq)
  exact Eq.trans
    (mixedImplication_normalizeSameOrder nestedEq nestedEq
      negation disjunction left right)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) nestedEq) right)) leftEq)
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p (sameDisjunction disjunction q r)))
        rightEq))

def rawStar16
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    Formula signature real []
      (max (max order order)
        (max (max order order) (max order order))) :=
  let pairEq := natMaxSelf order
  let consequentEq := natMaxCongr pairEq pairEq
  let resultEq := natMaxCongr pairEq consequentEq
  mixedImplication
    (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction resultEq.symm) disjunction)
    (mixedImplication negation
      (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q r)
    (mixedImplication
      (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
      (Eq.mp (congrArg signature.Disjunction consequentEq.symm) disjunction)
      (.disj
        (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q)
      (.disj
        (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p r))

theorem rawStar16_same
    (negation : signature.Negation order)
    (disjunction : signature.Disjunction order)
    (p q r : Formula signature real [] order) :
    let pairEq := natMaxSelf order
    let consequentEq := natMaxCongr pairEq pairEq
    let resultEq := natMaxCongr pairEq consequentEq
    Eq.mp (congrArg (Formula signature real []) resultEq)
        (rawStar16 negation disjunction p q r) =
      implication negation disjunction
        (implication negation disjunction q r)
        (implication negation disjunction
          (sameDisjunction disjunction p q)
          (sameDisjunction disjunction p r)) := by
  let pairEq := natMaxSelf order
  let consequentEq := natMaxCongr pairEq pairEq
  let antecedent := mixedImplication negation
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) q r
  let pq := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p q
  let pr := Formula.disj
    (Eq.mp (congrArg signature.Disjunction pairEq.symm) disjunction) p r
  let consequent := mixedImplication
    (Eq.mp (congrArg signature.Negation pairEq.symm) negation)
    (Eq.mp (congrArg signature.Disjunction consequentEq.symm) disjunction)
    pq pr
  have antecedentEq := mixedImplication_normalizeSameOrder
    rfl rfl negation disjunction q r
  have pqEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p q
  have prEq := Formula.disj_normalizeSameOrder rfl rfl disjunction p r
  have consequentStep := mixedImplication_normalizeSameOrder
    pairEq pairEq negation disjunction pq pr
  have consequentEq' := Eq.trans consequentStep
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) pairEq) pr)) pqEq)
      (congrArg (implication negation disjunction
          (sameDisjunction disjunction p q)) prEq))
  exact Eq.trans
    (mixedImplication_normalizeSameOrder pairEq consequentEq
      negation disjunction antecedent consequent)
    (Eq.trans
      (congrArg (fun formula => implication negation disjunction formula
          (Eq.mp (congrArg (Formula signature real []) consequentEq) consequent))
        antecedentEq)
      (congrArg (implication negation disjunction
          (implication negation disjunction q r)) consequentEq'))

#print axioms Formula.disj_normalizeSameOrder
#print axioms mixedImplication_normalizeSameOrder
#print axioms rawStar13_same
#print axioms rawStar14_same
#print axioms rawStar15_same
#print axioms rawStar16_same

end PM.RamifiedSyntax
