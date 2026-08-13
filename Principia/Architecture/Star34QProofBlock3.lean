import Principia.Architecture.Star34QProofBlock2

/-! # PM I, ✱34·34–4: eight consecutive relation theorems. -/

namespace PM.Architecture.Star34QProofBlock3

open PM.Architecture.Star34QProofBlock
open PM.Architecture.Star34QProofBlock2

/-- ✱34·34. Composition is monotone in both relation arguments. -/
theorem star_34_34 (R P : Relation α β) (S Q : Relation β γ) :
    included R P → included S Q → included (compose R S) (compose P Q) := by
  intro hRP hSQ x z
  rintro ⟨y, hxy, hyz⟩
  exact ⟨y, hRP x y hxy, hSQ y z hyz⟩

/-- ✱34·35. If a nonempty relation ends only where `P` begins, its
composition with `P` is nonempty. -/
theorem star_34_35 (R : Relation α β) (P : Relation β γ) :
    NonemptyRelation R →
      (∀ y, converseDomain R y → domain P y) →
      NonemptyRelation (compose R P) := by
  rintro ⟨x, y, hxy⟩ rangeIncluded
  obtain ⟨z, hyz⟩ := rangeIncluded y ⟨x, hxy⟩
  exact ⟨x, z, y, hxy, hyz⟩

/-- ✱34·351. The dual existence theorem for composition on the left. -/
theorem star_34_351 (R : Relation β γ) (P : Relation α β) :
    NonemptyRelation R →
      (∀ y, domain R y → converseDomain P y) →
      NonemptyRelation (compose P R) := by
  rintro ⟨y, z, hyz⟩ domainIncluded
  obtain ⟨x, hxy⟩ := domainIncluded y ⟨z, hyz⟩
  exact ⟨x, z, y, hxy, hyz⟩

/-- ✱34·36. The domain of a composite lies in the first domain, and its
converse domain lies in that of the second factor. -/
theorem star_34_36 (P : Relation α β) (Q : Relation β γ) :
    (∀ x, domain (compose P Q) x → domain P x) ∧
      (∀ z, converseDomain (compose P Q) z → converseDomain Q z) := by
  constructor
  · rintro x ⟨z, y, hxy, _⟩
    exact ⟨y, hxy⟩
  · rintro z ⟨x, y, _, hyz⟩
    exact ⟨y, hyz⟩

/-- ✱34·361. A middle relation whose two ends fit the outer factors yields
a nonempty triple composite. -/
theorem star_34_361 (R : Relation β γ) (P : Relation α β)
    (Q : Relation γ δ) :
    NonemptyRelation R →
      (∀ y, domain R y → converseDomain P y) →
      (∀ z, converseDomain R z → domain Q z) →
      NonemptyRelation (compose (compose P R) Q) := by
  rintro ⟨y, z, hyz⟩ leftFits rightFits
  obtain ⟨x, hxy⟩ := leftFits y ⟨z, hyz⟩
  obtain ⟨w, hzw⟩ := rightFits z ⟨y, hyz⟩
  exact ⟨x, w, z, ⟨y, hxy, hyz⟩, hzw⟩

/-- ✱34·37. The field of a composite is contained in the first domain
union the second converse domain. -/
theorem star_34_37 (P : Relation α α) (Q : Relation α α) :
    ∀ x, field (compose P Q) x → domain P x ∨ converseDomain Q x := by
  intro x
  rintro (⟨z, y, hxy, _⟩ | ⟨z, y, _, hyx⟩)
  · exact Or.inl ⟨y, hxy⟩
  · exact Or.inr ⟨y, hyx⟩

/-- ✱34·38. Hence the composite field is contained in the union of the
fields of its two factors. -/
theorem star_34_38 (P Q : Relation α α) :
    ∀ x, field (compose P Q) x → field P x ∨ field Q x := by
  intro x hx
  rcases star_34_37 P Q x hx with hP | hQ
  · exact Or.inl (Or.inl hP)
  · exact Or.inr (Or.inr hQ)

/-- ✱34·4. Two successive relation applications give an application of the
composite relation. -/
theorem star_34_4 (P : Relation α β) (Q : Relation β γ)
    (b : α) (c : β) (z : γ) :
    P b c → Q c z → compose P Q b z := by
  intro hbc hcz
  exact ⟨c, hbc, hcz⟩

end PM.Architecture.Star34QProofBlock3
