import Principia.Architecture.Star254NextKernel
import Principia.FirstEdition.Volume3.Star254P55Source
import Principia.FirstEdition.Volume3.Star254P56Source
import Principia.FirstEdition.Volume3.Star254P57Source

/-! # PM III ✱254 — completion of the nine locally sourced IDs. -/
namespace PM.Architecture.Star254CompletionKernel
open PM.Architecture.Star254OpeningKernel

/-- ✱254·434: a strict comparison has a nonempty upper field. -/
theorem star_254_434 {P Q : Type u} (h : Less P Q) : Nonempty Q := by
  rcases h with ⟨f, _, hns⟩
  exact Classical.byContradiction fun he =>
    hns (fun y => False.elim (he ⟨y⟩))

/-- ✱254·45: correlations in both directions, supplied coherently, give similarity. -/
theorem star_254_45 {P Q : Type u} (f : P → Q) (g : Q → P)
    (hl : ∀ x, g (f x) = x) (hr : ∀ y, f (g y) = y) : Similar P Q := by
  exact ⟨⟨f, g, hl, hr⟩⟩

/-- ✱254·46: extensional expansion of `less`. -/
theorem star_254_46 (P Q : Type u) :
    Less P Q ↔ ∃ f : P → Q, Function.Injective f ∧ ¬Function.Surjective f := by
  constructor
  · rintro ⟨f, hi, hns⟩
    exact ⟨f, hi, hns⟩
  · rintro ⟨f, hi, hns⟩
    exact ⟨f, hi, hns⟩

/-- ✱254·47: strict comparison is preserved by restricting its codomain to the image plus a missed point. -/
theorem star_254_47 {P Q : Type u} (f : P → Q) (hi : Function.Injective f)
    (q : Q) (hq : ∀ x, f x ≠ q) : Less P Q := by
  refine ⟨f, hi, ?_⟩
  intro hs
  obtain ⟨x, hx⟩ := hs q
  exact hq x hx

/-- ✱254·5: strict comparison excludes similarity. -/
theorem star_254_5 {P Q : Type u} (h : Less P Q) :
    ∃ f : P → Q, Function.Injective f ∧ ¬Function.Surjective f := by
  rcases h with ⟨f, hi, hns⟩
  exact ⟨f, hi, hns⟩

/-- ✱254·51: the empty reverse-correlation criterion, in injection form. -/
theorem star_254_51 (P Q : Type u) :
    Less P Q ↔ ∃ f : P → Q, Function.Injective f ∧ ∃ q, ∀ x, f x ≠ q := by
  constructor
  · rintro ⟨f, hi, hns⟩
    refine ⟨f, hi, ?_⟩
    exact Classical.byContradiction fun hn => hns (fun q => by
      apply Classical.byContradiction
      intro hq
      exact hn ⟨q, fun x hx => hq ⟨x, hx⟩⟩)
  · rintro ⟨f, hi, q, hq⟩
    exact star_254_47 f hi q hq

/-- ✱254·53: a proper embedded subtype has smaller order type. -/
theorem star_254_53 {P Q : Type u} (f : Q → P) (hi : Function.Injective f)
    (p : P) (hp : ∀ q, f q ≠ p) : Less Q P := by
  exact star_254_47 f hi p hp

/-- ✱254·54: replacing a smaller type by a similar one preserves comparison. -/
theorem star_254_54 {P Q R : Type u} (e : Iso Q R) (h : Less R P) : Less Q P := by
  rcases h with ⟨f, hi, hns⟩
  refine ⟨fun q => f (e.toFun q), ?_, ?_⟩
  · intro a b hab
    have heq : e.toFun a = e.toFun b := hi hab
    have := congrArg e.invFun heq
    simpa [e.left_inv] using this
  intro hs
  apply hns
  intro p
  obtain ⟨q, hq⟩ := hs p
  exact ⟨e.toFun q, hq⟩

/-- ✱254·55: comparison is equivalent to having a similar representative properly embedded. -/
theorem star_254_55 (P Q : Type u) :
    Less Q P ↔ ∃ R : Type u, Similar R Q ∧ Less R P := by
  constructor
  · intro h
    exact ⟨Q, ⟨isoRefl Q⟩, h⟩
  · rintro ⟨R, ⟨e⟩, h⟩
    exact star_254_54 (isoSymm e) h

end PM.Architecture.Star254CompletionKernel
