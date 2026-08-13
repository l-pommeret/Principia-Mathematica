import Principia.Architecture.Star73Prerequisites

/-! # PM I, ✱73·01–✱73·25: similarity of classes. -/

namespace PM.Architecture.Star73OpeningKernel
open PM.Architecture.Star73Prerequisites

def SimilarityWitness (a : Class A) (b : Class B) :=
  {R : Relation A B // OneOne R ∧ Domain R = a ∧ ConverseDomain R = b}

/-- ✱73·01, definition of similarity by a one-one correlating relation. -/
theorem star_73_01 (a : Class A) (b : Class B) :
    Similar a b ↔ ∃ R, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱73·02, the descriptive class of correlations witnessing similarity. -/
theorem star_73_02 (a : Class A) (b : Class B) :
    Nonempty (SimilarityWitness a b) ↔ Similar a b := by
  exact ⟨fun ⟨⟨R, h⟩⟩ => ⟨R, h⟩, fun ⟨R, h⟩ => ⟨⟨R, h⟩⟩⟩

/-- ✱73·03, expanded membership condition for similarity. -/
theorem star_73_03 (a : Class A) (b : Class B) :
    Similar a b ↔ ∃ R, Functional R ∧ Injective R ∧ Domain R = a ∧
      ConverseDomain R = b := by
  simp only [Similar, OneOne, and_assoc]

/-- ✱73·04, existence of a similarity correlation. -/
theorem star_73_04 (a : Class A) (b : Class B) :
    Similar a b ↔ Nonempty (SimilarityWitness a b) := (star_73_02 a b).symm

/-- ✱73·1, the fundamental existential form. -/
theorem star_73_1 (a : Class A) (b : Class B) :
    Similar a b ↔ ∃ R, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b := Iff.rfl

/-- ✱73·11, enlarge the domain and then restrict the correlation to `a`. -/
theorem star_73_11 (a : Class A) (b : Class B) :
    Similar a b ↔ ∃ R, OneOne R ∧ Included a (Domain R) ∧ b = Image R a := by
  constructor
  · rintro ⟨R, hR, hDa, hCb⟩
    refine ⟨R, hR, ?_, ?_⟩
    · intro x hx; rw [hDa]; exact hx
    · rw [← hCb]
      funext y; apply propext
      exact ⟨fun ⟨x, hxy⟩ => ⟨x, by rw [← hDa]; exact ⟨y, hxy⟩, hxy⟩,
        fun ⟨x, _, hxy⟩ => ⟨x, hxy⟩⟩
  · rintro ⟨R, hR, ha, rfl⟩
    refine ⟨RestrictDomain a R, oneOne_restrictDomain hR a, ?_, rfl⟩
    funext x; apply propext
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => let ⟨y, hxy⟩ := ha hx; ⟨y, hx, hxy⟩⟩

/-- ✱73·12, the converse range-restriction form. -/
theorem star_73_12 (a : Class A) (b : Class B) :
    Similar a b ↔ ∃ R, OneOne R ∧ Included b (ConverseDomain R) ∧ a = Preimage R b := by
  constructor
  · rintro ⟨R, hR, hDa, hCb⟩
    refine ⟨R, hR, ?_, ?_⟩
    · intro y hy; rw [hCb]; exact hy
    · rw [← hDa]
      funext x; apply propext
      exact ⟨fun ⟨y, hxy⟩ => ⟨y, by rw [← hCb]; exact ⟨x, hxy⟩, hxy⟩,
        fun ⟨y, _, hxy⟩ => ⟨y, hxy⟩⟩
  · rintro ⟨R, hR, hb, rfl⟩
    refine ⟨RestrictRange R b, oneOne_restrictRange hR b, ?_, ?_⟩
    · exact (preimage_eq_domain_restrict R b).symm
    · funext y; apply propext
      exact ⟨fun ⟨_, _, hy⟩ => hy, fun hy => let ⟨x, hxy⟩ := hb hy; ⟨x, hxy, hy⟩⟩

/-- ✱73·13, a one-one relation induces a one-one map on its image classes. -/
theorem star_73_13 {R : Relation A B} (hR : OneOne R) {p q : Class A}
    (hp : Included p (Domain R)) (hq : Included q (Domain R)) :
    Image R p = Image R q → p = q := by
  intro h; funext x; apply propext; constructor
  · intro hx; obtain ⟨y, hxy⟩ := hp hx
    obtain ⟨z, hz, hzy⟩ : Image R q y := by rw [← h]; exact ⟨x, hx, hxy⟩
    simpa [hR.2 hxy hzy] using hz
  · intro hx; obtain ⟨y, hxy⟩ := hq hx
    obtain ⟨z, hz, hzy⟩ : Image R p y := by rw [h]; exact ⟨x, hx, hxy⟩
    simpa [hR.2 hxy hzy] using hz

/-- ✱73·131, the preceding class-image result under an explicit domain condition. -/
theorem star_73_131 {R : Relation A B} (hR : OneOne R) {p q : Class A}
    (hp : Included p (Domain R)) (hq : Included q (Domain R)) :
    Image R p = Image R q ↔ p = q := by
  constructor
  · exact star_73_13 hR hp hq
  · rintro rfl; rfl

/-- ✱73·14, pointwise equality characterizes injectivity of an image map. -/
theorem star_73_14 {R : Relation A B} (hR : OneOne R) {p q : Class A}
    (hp : Included p (Domain R)) (hq : Included q (Domain R)) :
    Image R p = Image R q ↔ ∀ x, p x ↔ q x := by
  rw [star_73_131 hR hp hq]
  exact ⟨fun h x => by rw [h], fun h => by funext x; exact propext (h x)⟩

/-- ✱73·141, the converse-image version of ✱73·14. -/
theorem star_73_141 {R : Relation A B} (hR : OneOne R) {p q : Class B}
    (hp : Included p (ConverseDomain R)) (hq : Included q (ConverseDomain R)) :
    Preimage R p = Preimage R q ↔ ∀ y, p y ↔ q y := by
  simpa [Preimage, Image, Converse] using
    (star_73_14 (R := Converse R) ((oneOne_converse).2 hR) hp hq)

/-- ✱73·142, restricting a relation to a class preserves one-one-ness. -/
theorem star_73_142 {R : Relation A B} (hR : OneOne R) (b : Class B) :
    OneOne (RestrictRange R b) := oneOne_restrictRange hR b

/-- ✱73·15, range restriction supplies a similarity correlation. -/
theorem star_73_15 {R : Relation A B} (hR : OneOne R) (b : Class B)
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b := by
  exact (star_73_12 _ _).2 ⟨R, hR, hb, rfl⟩

/-- ✱73·21, an image under a one-one relation is similar to its source. -/
theorem star_73_21 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a := by
  have h := (star_73_11 a (Image R a)).2 ⟨R, hR, ha, rfl⟩
  rcases h with ⟨S, hS, hD, hC⟩
  exact ⟨Converse S, (oneOne_converse).2 hS, hC, hD⟩

/-- ✱73·22, a restricted converse image is similar to its source class. -/
theorem star_73_22 {R : Relation A B} (hR : OneOne R) (b : Class B)
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b :=
  star_73_15 hR b hb

/-- ✱73·23, the class-image formulation. -/
theorem star_73_23 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a := star_73_21 hR a ha

/-- ✱73·231, the converse class-image formulation. -/
theorem star_73_231 {R : Relation A B} (hR : OneOne R) (b : Class B)
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b :=
  star_73_22 hR b hb

/-- ✱73·24, equality of values yields similarity of the range and domain. -/
theorem star_73_24 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a := star_73_21 hR a ha

/-- ✱73·241, converse form of ✱73·24. -/
theorem star_73_241 {R : Relation A B} (hR : OneOne R) (b : Class B)
    (hb : Included b (ConverseDomain R)) : Similar (Preimage R b) b :=
  star_73_22 hR b hb

/-- ✱73·25, a single-valued injective assignment has range similar to its domain. -/
theorem star_73_25 {R : Relation A B} (hfun : Functional R) (hinj : Injective R)
    (a : Class A) (ha : Included a (Domain R)) : Similar (Image R a) a :=
  star_73_21 ⟨hfun, hinj⟩ a ha

end PM.Architecture.Star73OpeningKernel
