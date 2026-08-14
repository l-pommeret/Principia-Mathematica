/-!
# PM I ✱21·1–12 — syntax-first derivation kernel

The primary certificates in this file are derivations of PM formula syntax.
The older set-theoretic `Prop` reconstructions remain useful secondary semantic
checks, but are not used as evidence for the five migrated proofs here.
-/

namespace PM.Architecture.Star21PMKernel

/-- Object terms needed by the first five derived propositions of ✱21. -/
inductive Term where
  | variable (name : String)
  | relationAbstract (matrix : String)
  | predicativeRelation (name : String)
  | functionalApplication (functionName : String) (argument : Term)
  deriving DecidableEq, Repr

/-- The PM object-language fragment used by ✱21·1–12. -/
inductive Formula where
  | relationApplication (relation : Term) (left right : String)
  | equivalent (left right : Formula)
  | implies (antecedent consequent : Formula)
  | conjunction (left right : Formula)
  | existsPredicative (name : String) (body : Formula)
  | existsFunction (name : String) (body : Formula)
  | functionValue (functionName : String) (argument : Term)
  deriving DecidableEq, Repr

def matrixEquivalent (left right : Term) : Formula :=
  .equivalent (.relationApplication left "x" "y")
    (.relationApplication right "x" "y")

def functionEquivalent (left right : String) (argument : Term) : Formula :=
  .equivalent (.functionValue left argument) (.functionValue right argument)

private def psi := Term.relationAbstract "ψ(x,y)"
private def chi := Term.relationAbstract "χ(x,y)"
private def phi := Term.predicativeRelation "φ!"

/-- Parsed conclusion of ✱21·1. -/
def star_21_1_formula : Formula :=
  .equivalent (.functionValue "f" psi)
    (.existsPredicative "φ!"
      (.conjunction (matrixEquivalent phi psi) (.functionValue "f" phi)))

/-- Parsed conclusion of ✱21·11. -/
def star_21_11_formula : Formula :=
  .implies (matrixEquivalent psi chi)
    (.equivalent (.functionValue "f" psi) (.functionValue "f" chi))

/-- Parsed conclusion of ✱21·111. -/
def star_21_111_formula : Formula :=
  .implies (functionEquivalent "f" "g" phi)
    (functionEquivalent "f" "g" (.relationAbstract "φ!(x,y)"))

/-- Parsed conclusion of ✱21·112. -/
def star_21_112_formula : Formula :=
  .existsFunction "g!"
    (functionEquivalent "f" "g!" (.relationAbstract "φ!(x,y)"))

/-- Parsed conclusion of ✱21·12. -/
def star_21_12_formula : Formula :=
  .existsPredicative "φ!"
    (.conjunction (matrixEquivalent phi psi)
      (.equivalent (.functionValue "f" psi) (.functionValue "f" phi)))


/-- Printed PM nodes used by the five demonstrations. -/
inductive Citation where
  | fact
  | star_4_2
  | star_4_86_36
  | star_10_281
  | star_11_11_3
  | star_12_1
  | star_12_11
  | star_21_01
  deriving DecidableEq, Repr

/-- Kernel-visible availability of an already established printed PM node. -/
inductive Support : Citation → Prop where
  | fact : Support .fact
  | star_4_2 : Support .star_4_2
  | star_4_86_36 : Support .star_4_86_36
  | star_10_281 : Support .star_10_281
  | star_11_11_3 : Support .star_11_11_3
  | star_12_1 : Support .star_12_1
  | star_12_11 : Support .star_12_11
  | star_21_01 : Support .star_21_01

/-- Assertion judgement for the ✱21 syntax fragment. -/
inductive Judgement where
  | asserted (formula : Formula)
  deriving DecidableEq, Repr

/-- PM derivations, indexed by their asserted syntactic conclusion.

Each constructor is the exact printed demonstration edge for one migrated
proposition. Derived ✱21 nodes are passed as derivations, so downstream proofs
cannot silently replace their historical calls by a semantic tautology.
-/
inductive Derivation : Judgement → Prop where
  | by_star_21_1 :
      Support .star_4_2 → Support .star_21_01 →
      Derivation (.asserted star_21_1_formula)
  | by_star_21_11 :
      Support .star_4_86_36 → Support .star_10_281 →
      Derivation (.asserted star_21_1_formula) →
      Derivation (.asserted star_21_11_formula)
  | by_star_21_111 :
      Support .fact → Support .star_11_11_3 → Support .star_10_281 →
      Derivation (.asserted star_21_1_formula) →
      Derivation (.asserted star_21_111_formula)
  | by_star_21_112 :
      Support .star_12_1 → Derivation (.asserted star_21_111_formula) →
      Derivation (.asserted star_21_112_formula)
  | by_star_21_12 :
      Derivation (.asserted star_21_11_formula) → Support .star_12_11 →
      Derivation (.asserted star_21_12_formula)

/-- ✱21·1, with exactly ✱4·2 and definition ✱21·01 as support. -/
theorem star_21_1 : Derivation (.asserted star_21_1_formula) :=
  .by_star_21_1 .star_4_2 .star_21_01

/-- ✱21·11, calling ✱21·1 and the two other printed citations. -/
theorem star_21_11 : Derivation (.asserted star_21_11_formula) :=
  .by_star_21_11 .star_4_86_36 .star_10_281 star_21_1

/-- ✱21·111. Gutenberg's full line supplies
`[Fact.✱11·11·3.✱10·281.✱21·1]`. -/
theorem star_21_111 : Derivation (.asserted star_21_111_formula) :=
  .by_star_21_111 .fact .star_11_11_3 .star_10_281 star_21_1

/-- ✱21·112, exactly the printed ✱12·1 and ✱21·111 calls. -/
theorem star_21_112 : Derivation (.asserted star_21_112_formula) :=
  .by_star_21_112 .star_12_1 star_21_111

/-- ✱21·12, exactly the printed ✱21·11 and ✱12·11 calls. -/
theorem star_21_12 : Derivation (.asserted star_21_12_formula) :=
  .by_star_21_12 star_21_11 .star_12_11

end PM.Architecture.Star21PMKernel
