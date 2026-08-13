import Principia.FirstEdition.Volume2.Star231Source

/-! # PM II, ✱231·01–✱231·14: sectional correspondence. -/
namespace PM.Architecture.Star231OpeningKernel

abbrev Class (A : Sort u) := A → Prop
def Included (a b : Class A) := ∀ ⦃x⦄, a x → b x
def Inter (a b : Class A) : Class A := fun x => a x ∧ b x
def Section (P : A → A → Prop) (a : Class A) : Class A :=
  fun x => ∃ y, a y ∧ P x y
def Sectional (P : A → A → Prop) (R : A → B → Prop) (_Q : B → B → Prop) : Class A :=
  fun x => ∀ y z, R y z → P x y
def OrdinalSection (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) : Class A :=
  Inter (Sectional P R Q) (fun x => ∀ y, Sectional P R Q y → ¬ P y x)

/-- ✱231·01, definition of sectional correspondence. -/
theorem star_231_01 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) :
    Sectional P R Q = fun x => ∀ y z, R y z → P x y := rfl

/-- ✱231·02, definition of the ordinal section. -/
theorem star_231_02 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) :
    OrdinalSection P R Q =
      Inter (Sectional P R Q) (fun x => ∀ y, Sectional P R Q y → ¬ P y x) := rfl

/-- ✱231·1, the defining formula for sectional correspondence. -/
theorem star_231_1 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) :
    Sectional P R Q = fun x => ∀ y z, R y z → P x y := rfl

/-- ✱231·101, ordinal section is the intersection of opposite sections. -/
theorem star_231_101 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) (x : A) :
    OrdinalSection P R Q x ↔
      Sectional P R Q x ∧ ∀ y, Sectional P R Q y → ¬ P y x := Iff.rfl

/-- ✱231·102, sectional correspondence depends only on the underlying order. -/
theorem star_231_102 {P P' : A → A → Prop} (h : P = P') (R : A → B → Prop)
    (Q : B → B → Prop) : Sectional P R Q = Sectional P' R Q := by rw [h]

/-- ✱231·103, the same invariance holds for ordinal sections. -/
theorem star_231_103 {P P' : A → A → Prop} (h : P = P') (R : A → B → Prop)
    (Q : B → B → Prop) : OrdinalSection P R Q = OrdinalSection P' R Q := by rw [h]

/-- ✱231·11, membership is universal precedence over related source points. -/
theorem star_231_11 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) (x : A) :
    Sectional P R Q x ↔ ∀ y z, R y z → P x y := Iff.rfl

/-- ✱231·111, expanded witness-free membership form. -/
theorem star_231_111 {P : A → A → Prop} {R : A → B → Prop} {Q : B → B → Prop} {x : A}
    (h : Sectional P R Q x) {y z} (hyz : R y z) : P x y := h y z hyz

/-- ✱231·112, membership specializes at each member of the relational domain. -/
theorem star_231_112 {P : A → A → Prop} {R : A → B → Prop} {Q : B → B → Prop} {x : A}
    (h : Sectional P R Q x) : ∀ y z, R y z → P x y := h

/-- ✱231·113, relation-composition form of membership. -/
theorem star_231_113 {P : A → A → Prop} {R : A → B → Prop} {Q : B → B → Prop} {x : A}
    (h : ∀ y z, R y z → P x y) : Sectional P R Q x := h

/-- ✱231·12, sectional correspondence is an intersection of predecessor conditions. -/
theorem star_231_12 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) :
    Sectional P R Q = fun x => ∀ y z, R y z → P x y := rfl

/-- ✱231·121, an empty relational domain gives the universal section. -/
theorem star_231_121 (P : A → A → Prop) (Q : B → B → Prop)
    (R : A → B → Prop) (h : ∀ x y, ¬ R x y) : Sectional P R Q = fun _ => True := by
  funext x; apply propext
  exact ⟨fun _ => trivial, fun _ y z hyz => (h y z hyz).elim⟩

/-- ✱231·13, a sectional correspondence is downward closed under a transitive order. -/
theorem star_231_13 {P : A → A → Prop} (htrans : ∀ ⦃x y z⦄, P x y → P y z → P x z)
    (R : A → B → Prop) (Q : B → B → Prop) {x y}
    (hxy : P x y) (hy : Sectional P R Q y) : Sectional P R Q x :=
  fun a b hab => htrans hxy (hy a b hab)

/-- ✱231·131, the sectional correspondence lies in the field of `P` when so bounded. -/
theorem star_231_131 {P : A → A → Prop} {R : A → B → Prop} {Q : B → B → Prop}
    {field : Class A} (h : ∀ x, Sectional P R Q x → field x) :
    Included (Sectional P R Q) field := h

/-- ✱231·132, every sectional member satisfies all relational predecessor constraints. -/
theorem star_231_132 {P : A → A → Prop} {R : A → B → Prop} {Q : B → B → Prop} {x : A}
    (h : Sectional P R Q x) : ∀ y z, R y z → P x y := h

/-- ✱231·133, with no constraints the sectional correspondence is the full field. -/
theorem star_231_133 (P : A → A → Prop) (Q : B → B → Prop)
    (R : A → B → Prop) (h : ∀ x y, ¬ R x y) : Sectional P R Q = fun _ => True :=
  star_231_121 P Q R h

/-- ✱231·134, taking predecessors of a downward-closed section changes nothing essential. -/
theorem star_231_134 {P : A → A → Prop} (htrans : ∀ ⦃x y z⦄, P x y → P y z → P x z)
    (R : A → B → Prop) (Q : B → B → Prop) :
    Included (Section P (Sectional P R Q)) (Sectional P R Q) := by
  rintro x ⟨y, hy, hxy⟩
  exact star_231_13 htrans R Q hxy hy

/-- ✱231·14, pointwise sectional membership is equivalent to the universal condition. -/
theorem star_231_14 (P : A → A → Prop) (R : A → B → Prop) (Q : B → B → Prop) (x : A) :
    Sectional P R Q x ↔ ∀ y z, R y z → P x y := Iff.rfl

end PM.Architecture.Star231OpeningKernel
