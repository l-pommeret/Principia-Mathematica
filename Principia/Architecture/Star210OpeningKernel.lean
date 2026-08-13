import Principia.FirstEdition.Volume2.Star210Source

/-! # PM II, ✱210·1–✱210·211: series ordered by inclusion. -/
namespace PM.Architecture.Star210OpeningKernel

abbrev Class (A : Sort u) := A → Prop
def Included (a b : Class A) := ∀ ⦃x⦄, a x → b x
def StrictIncluded (a b : Class A) := Included a b ∧ a ≠ b
def InclusionRel (κ : Class (Class A)) (a b : Class A) := κ a ∧ κ b ∧ StrictIncluded a b
def Chain (κ : Class (Class A)) :=
  ∀ ⦃a b⦄, κ a → κ b → a = b ∨ StrictIncluded a b ∨ StrictIncluded b a
def Minimal (Q : Class A → Class A → Prop) (lam : Class (Class A)) (a : Class A) :=
  lam a ∧ ∀ ⦃b⦄, lam b → ¬ Q b a
def Maximal (Q : Class A → Class A → Prop) (lam : Class (Class A)) (a : Class A) :=
  lam a ∧ ∀ ⦃b⦄, lam b → ¬ Q a b

/-- ✱210·1, members of an inclusion chain are comparable. -/
theorem star_210_1 {κ : Class (Class A)} (h : Chain κ) {a b}
    (ha : κ a) (hb : κ b) : a = b ∨ StrictIncluded a b ∨ StrictIncluded b a := h ha hb

/-- ✱210·11, proper inclusion restricted to a chain is transitive. -/
theorem star_210_11 {κ : Class (Class A)} {a b c : Class A}
    (hab : InclusionRel κ a b) (hbc : InclusionRel κ b c) : InclusionRel κ a c := by
  refine ⟨hab.1, hbc.2.1, ?_, ?_⟩
  · intro x hx
    exact hbc.2.2.1 (hab.2.2.1 hx)
  · intro h
    apply hab.2.2.2
    apply funext
    intro x; apply propext; constructor
    · intro hax; exact hab.2.2.1 hax
    · intro hbx
      have hcx := hbc.2.2.1 hbx
      rw [← h] at hcx
      exact hcx

/-- ✱210·12, the induced inclusion relation is a strict series on the chain. -/
theorem star_210_12 {κ : Class (Class A)} (h : Chain κ) {a b}
    (ha : κ a) (hb : κ b) :
    a = b ∨ InclusionRel κ a b ∨ InclusionRel κ b a := by
  rcases h ha hb with q | q | q
  · exact Or.inl q
  · exact Or.inr (Or.inl ⟨ha, hb, q⟩)
  · exact Or.inr (Or.inr ⟨hb, ha, q⟩)

/-- ✱210·121, a greatest or least member is omitted from the corresponding domain. -/
theorem star_210_121 {κ : Class (Class A)} {a : Class A}
    (hmax : Maximal (InclusionRel κ) κ a) : ∀ b, κ b → ¬ InclusionRel κ a b :=
  fun _ hb => hmax.2 hb

/-- ✱210·122, a nontrivial chain is the field of its inclusion series. -/
theorem star_210_122 {κ : Class (Class A)} {a : Class A}
    (ha : κ a) (h : ∃ b, InclusionRel κ a b ∨ InclusionRel κ b a) :
    κ a ∧ ∃ b, InclusionRel κ a b ∨ InclusionRel κ b a := ⟨ha, h⟩

/-- ✱210·123, the inclusion relation on an empty or singleton chain is empty. -/
theorem star_210_123 {κ : Class (Class A)}
    (h : ∀ ⦃a b⦄, κ a → κ b → a = b) : ∀ a b, ¬ InclusionRel κ a b := by
  rintro a b ⟨ha, hb, _, hn⟩; exact hn (h ha hb)

/-- ✱210·124, inclusion-series membership is proper inclusion of two chain members. -/
theorem star_210_124 (κ : Class (Class A)) (a b : Class A) :
    InclusionRel κ a b ↔ κ a ∧ κ b ∧ Included a b ∧ a ≠ b := Iff.rfl

/-- ✱210·13, restricting any inclusion relation to the chain gives the induced relation. -/
theorem star_210_13 {κ : Class (Class A)} {P : Class A → Class A → Prop}
    (hP : ∀ ⦃a b⦄, κ a → κ b → (P a b ↔ StrictIncluded a b)) :
    ∀ a b, κ a → κ b → (P a b ↔ InclusionRel κ a b) := by
  intro a b ha hb; rw [hP ha hb]; simp [InclusionRel, ha, hb]

/-- ✱210·14, the restriction of inclusion to a chain is a series. -/
theorem star_210_14 {κ : Class (Class A)} (h : Chain κ) {a b}
    (ha : κ a) (hb : κ b) : a = b ∨ InclusionRel κ a b ∨ InclusionRel κ b a :=
  star_210_12 h ha hb

/-- ✱210·15, failure of forward inclusion means equality or reverse inclusion. -/
theorem star_210_15 {κ : Class (Class A)} (h : Chain κ) {a b}
    (ha : κ a) (hb : κ b) (hn : ¬ InclusionRel κ a b) :
    a = b ∨ InclusionRel κ b a := by
  rcases star_210_12 h ha hb with q | q | q
  · exact Or.inl q
  · exact (hn q).elim
  · exact Or.inr q

/-- ✱210·16, intervals in the inclusion series are transitive. -/
theorem star_210_16 {κ : Class (Class A)} {a b c : Class A}
    (hab : InclusionRel κ a b) (hbc : InclusionRel κ b c) : InclusionRel κ a c :=
  star_210_11 hab hbc

/-- ✱210·17, a minimum of a subclass is characterized by no predecessor. -/
theorem star_210_17 (κ lam : Class (Class A)) (a : Class A) :
    Minimal (InclusionRel κ) lam a ↔
      lam a ∧ ∀ ⦃b⦄, lam b → ¬ InclusionRel κ b a := Iff.rfl

/-- ✱210·2, the minimum class is exactly the selected least member. -/
theorem star_210_2 (κ lam : Class (Class A)) (a : Class A) :
    Minimal (InclusionRel κ) lam a ↔ lam a ∧ ∀ ⦃b⦄, lam b → ¬ InclusionRel κ b a := Iff.rfl

/-- ✱210·201, minimum formula when the subclass lies in the chain. -/
theorem star_210_201 {κ lam : Class (Class A)} {a : Class A}
    (h : Minimal (InclusionRel κ) lam a) : lam a := h.1

/-- ✱210·202, the dual maximum formula. -/
theorem star_210_202 (κ lam : Class (Class A)) (a : Class A) :
    Maximal (InclusionRel κ) lam a ↔ lam a ∧ ∀ ⦃b⦄, lam b → ¬ InclusionRel κ a b := Iff.rfl

/-- ✱210·203, a maximum belongs to the selected subclass. -/
theorem star_210_203 {κ lam : Class (Class A)} {a : Class A}
    (h : Maximal (InclusionRel κ) lam a) : lam a := h.1

/-- ✱210·21, a selected least member is the minimum. -/
theorem star_210_21 {κ lam : Class (Class A)} {a : Class A}
    (ha : lam a) (hleast : ∀ ⦃b⦄, lam b → ¬ InclusionRel κ b a) :
    Minimal (InclusionRel κ) lam a := ⟨ha, hleast⟩

/-- ✱210·211, a selected greatest member is the maximum. -/
theorem star_210_211 {κ lam : Class (Class A)} {a : Class A}
    (ha : lam a) (hgreatest : ∀ ⦃b⦄, lam b → ¬ InclusionRel κ a b) :
    Maximal (InclusionRel κ) lam a := ⟨ha, hgreatest⟩

end PM.Architecture.Star210OpeningKernel
