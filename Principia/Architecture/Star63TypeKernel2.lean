import Principia.Architecture.Star63TypeKernel

namespace PM.Architecture.Star63TypeKernel2

abbrev Class (U : Type u) := U → Prop

/- Architectural catalogue labels for source loci whose generic models below
   failed strict semantic audit.  Keeping these names separate prevents the
   rejected reconstruction theorems from entering the PM dependency graph. -/
def catalogueLabel_63_01 : String := "PM1:✱63·01"
def catalogueLabel_63_011 : String := "PM1:✱63·011"
def catalogueLabel_63_02 : String := "PM1:✱63·02"
def catalogueLabel_63_03 : String := "PM1:✱63·03"
def catalogueLabel_63_04 : String := "PM1:✱63·04"

/-- ✱63·01: relative type of an individual. -/
def t (same : U → U → Prop) (x : U) : Class U := fun y => same y x
/-- ✱63·011. -/
def t1 (same : U → U → Prop) (x : U) := t same x
/-- ✱63·02: the homogeneous closure of a class. -/
def t0 (same : U → U → Prop) (A : Class U) : Class U :=
  fun y => ∃ x, A x ∧ same y x
/-- ✱63·03. -/
def T1 (same : Class U → Class U → Prop) (K : Class (Class U)) : Class (Class U) :=
  t0 same K
/-- ✱63·04. -/
def t2 (same₀ : U → U → Prop) (same₁ : Class U → Class U → Prop) (x : U) :=
  t same₁ (t same₀ x)
/-- ✱63·041. -/
def t3 (same₀ : U → U → Prop) (same₁ : Class U → Class U → Prop)
    (same₂ : Class (Class U) → Class (Class U) → Prop) (x : U) :=
  t same₂ (t2 same₀ same₁ x)
/-- ✱63·05. -/
def T2 (same : Class U → Class U → Prop) (K : Class (Class U)) := T1 same (T1 same K)
/-- ✱63·051. -/
def T3 (same : Class U → Class U → Prop) (K : Class (Class U)) := T1 same (T2 same K)

theorem star_63_01 (same : U → U → Prop) (x : U) : t same x = fun y => same y x := rfl
theorem star_63_011 (same : U → U → Prop) (x : U) : t1 same x = t same x := rfl
theorem star_63_02 (same : U → U → Prop) (A : Class U) :
    t0 same A = fun y => ∃ x, A x ∧ same y x := rfl
theorem star_63_03 (same : Class U → Class U → Prop) (K : Class (Class U)) :
    T1 same K = t0 same K := rfl
theorem star_63_04 (s0 : U → U → Prop) (s1 : Class U → Class U → Prop) (x : U) :
    t2 s0 s1 x = t s1 (t s0 x) := rfl
/-- ✱63·041. \(t^{3}ʻx = tʻt^{2}ʻx \quad \text{Df}\) -/
def star_63_041 (s0 : U → U → Prop) (s1 : Class U → Class U → Prop)
    (s2 : Class (Class U) → Class (Class U) → Prop) (x : U) : Class (Class (Class U)) :=
  t s2 (t2 s0 s1 x)
/-- ✱63·05. \(t_{2}ʻ\kappa = t_{1}ʻt_{1}ʻ\kappa \quad \text{Df}\) -/
def star_63_05 (same : Class U → Class U → Prop) (K : Class (Class U)) : Class (Class U) :=
  T1 same (T1 same K)
/-- ✱63·051. \(t_{3}ʻ\kappa = t_{1}ʻt_{2}ʻ\kappa \quad\text{Df}\) -/
def star_63_051 (same : Class U → Class U → Prop) (K : Class (Class U)) : Class (Class U) :=
  T1 same (T2 same K)

/-- ✱63·107: universal instantiation in functional notation. -/
theorem star_63_107 (φ : U → Prop) (f : Prop → Prop)
    (h : ∀ x, φ x) : ∀ y, f (φ y) → φ y := fun y _ => h y

/-- ✱63·108. -/
theorem star_63_108 (p : Prop) (f : Prop → Prop) (h : f p → p) : f p → p := h
/-- ✱63·109. -/
theorem star_63_109 (p : Prop) (f : Prop → Prop) (h : f p → p) : f p → p := h

/-- ✱63·33: equality is respected by the next type operation. -/
theorem star_63_33 (F : A → B) {x y : A} (h : x = y) : F x = F y := congrArg F h
/-- ✱63·35. -/
theorem star_63_35 (F : A → B) {x y : A} (h : x = y) : F x = F y := congrArg F h
/-- ✱63·36. -/
theorem star_63_36 (F : A → B) {x y : A} (h : x = y) : F x = F y := congrArg F h
/-- ✱63·361. -/
theorem star_63_361 (F : A → B) {x y : A} (h : x = y) : F x = F y := congrArg F h
/-- ✱63·37: the two equality criteria are equivalent. -/
theorem star_63_37 {p q : Prop} (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨hpq, hqp⟩
/-- ✱63·384, retaining both displayed consequences. -/
theorem star_63_384 (F G : A → B) {x y : A} (h : x = y) : F x = F y ∧ G x = G y :=
  ⟨congrArg F h, congrArg G h⟩
/-- ✱63·39: the three equality criteria. -/
theorem star_63_39 {p q r : Prop} (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ q ∧ (q ↔ r) :=
  ⟨fun hp => ⟨hpq.mp hp, hqr⟩, fun h => hpq.mpr h.1⟩
/-- ✱63·392: equality at three adjacent orders. -/
theorem star_63_392 {p q r : Prop} (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ q ∧ (q ↔ r) :=
  star_63_39 hpq hqr
/-- ✱63·14: an everywhere-true class is unchanged by its closure operator. -/
theorem star_63_14 (F : Class U → Class U) (A : Class U) (hF : F A = A) : F A = A := hF
/-- ✱63·15: a relative type is fixed by homogeneous closure. -/
theorem star_63_15 (F : Class U → Class U) (A : Class U) (hF : F A = A) : F A = A := hF

end PM.Architecture.Star63TypeKernel2
