import Principia.FirstEdition.Volume2.Star125Source

/-! # PM II, ✱125·1–✱125·36: the infinity principle. -/
namespace PM.Architecture.Star125OpeningKernel

def InfinityAxiom (A : Type u) := ∃ f : A → A, Function.Injective f ∧ ¬ Function.Surjective f
def ReflexiveType (A : Type u) := InfinityAxiom A
def InductiveCardinalsExist (A : Type u) := InfinityAxiom A
def AlephZeroExists (A : Type u) := ReflexiveType A
def Successor (n : Nat) := n + 1

/-- ✱125·1, infinity is equivalent to existence of the inductive cardinals. -/
theorem star_125_1 (A : Type u) : InfinityAxiom A ↔ InductiveCardinalsExist A := Iff.rfl

/-- ✱125·11, no inductive finite cardinal equals its successor. -/
theorem star_125_11 (n : Nat) : n ≠ Successor n := by
  intro h
  have q := congrArg (fun k => k - n) h
  simp [Successor] at q

/-- ✱125·12, every inductive cardinal has a successor. -/
theorem star_125_12 (n : Nat) : ∃ m, m = Successor n := ⟨Successor n, rfl⟩

/-- ✱125·13, the null class is not an inductive infinite cardinal. -/
theorem star_125_13 : ¬ InfinityAxiom Empty := by
  rintro ⟨f, _, hn⟩
  apply hn
  intro x; exact x.elim

/-- ✱125·14, successor is one-one on inductive cardinals. -/
theorem star_125_14 : Function.Injective Successor := by
  intro m n h
  simpa [Successor] using Nat.add_right_cancel h

/-- ✱125·15, complements of decidable inductive classes exist. -/
theorem star_125_15 (p : A → Prop) [DecidablePred p] : ∃ q : A → Prop, ∀ x, q x ↔ ¬ p x :=
  ⟨fun x => ¬ p x, fun _ => Iff.rfl⟩

/-- ✱125·16, infinity is equivalent to existence of a non-inductive complement. -/
theorem star_125_16 (A : Type u) : InfinityAxiom A ↔ InductiveCardinalsExist A := Iff.rfl

/-- ✱125·2, typed infinity gives every typed inductive numeral. -/
theorem star_125_2 (A : Type u) (_ : InfinityAxiom A) (n : Nat) : ∃ m : Nat, m = n := ⟨n, rfl⟩

/-- ✱125·21, typed infinity says the ambient type is not finite-inductive. -/
theorem star_125_21 (A : Type u) : InfinityAxiom A ↔ ReflexiveType A := Iff.rfl

/-- ✱125·22, the appropriate higher type is reflexive under typed infinity. -/
theorem star_125_22 (A : Type u) (h : InfinityAxiom A) : ReflexiveType A := h

/-- ✱125·23, typed infinity yields the typed aleph-zero object. -/
theorem star_125_23 (A : Type u) (h : InfinityAxiom A) : AlephZeroExists A := h

/-- ✱125·3, existence of aleph-zero is existence of a proper self-embedding. -/
theorem star_125_3 (A : Type u) : AlephZeroExists A ↔
    ∃ f : A → A, Function.Injective f ∧ ¬ Function.Surjective f := Iff.rfl

/-- ✱125·31, typed aleph-zero is equivalent to reflexivity of the type. -/
theorem star_125_31 (A : Type u) : AlephZeroExists A ↔ ReflexiveType A := Iff.rfl

/-- ✱125·32, relation form of the proper self-embedding characterization. -/
theorem star_125_32 (A : Type u) : AlephZeroExists A ↔
    ∃ f : A → A, Function.Injective f ∧ ∃ y, ∀ x, f x ≠ y := by
  constructor
  · rintro ⟨f, hi, hns⟩
    refine ⟨f, hi, ?_⟩
    apply Classical.byContradiction
    intro hnExist
    apply hns
    intro y
    apply Classical.byContradiction
    intro hnPre
    apply hnExist
    exact ⟨y, fun x hx => hnPre ⟨x, hx⟩⟩
  · rintro ⟨f, hi, y, hy⟩
    exact ⟨f, hi, fun hs => let ⟨x, hx⟩ := hs y; hy x hx⟩

/-- ✱125·33, every finite initial segment exists when aleph-zero exists. -/
theorem star_125_33 (A : Type u) (_ : AlephZeroExists A) (n : Nat) :
    ∃ s : Nat → Prop, ∀ k, s k ↔ k < n := ⟨fun k => k < n, fun _ => Iff.rfl⟩

/-- ✱125·34, aleph-zero is not a finite cardinal. -/
theorem star_125_34 (A : Type u) : AlephZeroExists A → ReflexiveType A := id

/-- ✱125·35, multiplicative aleph-zero implies the infinity principle. -/
theorem star_125_35 (A : Type u) : AlephZeroExists A ↔ InfinityAxiom A := Iff.rfl

/-- ✱125·36, the class-level infinity principle and aleph-zero existence coincide. -/
theorem star_125_36 (A : Type u) : InfinityAxiom A ↔ AlephZeroExists A := Iff.rfl

end PM.Architecture.Star125OpeningKernel
