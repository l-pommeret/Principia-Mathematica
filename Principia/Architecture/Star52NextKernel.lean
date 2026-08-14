import Principia.Architecture.Star52OpeningKernel

namespace PM.Architecture.Star52NextKernel

open PM.Architecture.Star52OpeningKernel

/-- The contextual condition that `x` is the unique member described by
`(℩x)(x ∈ A)`. -/
def uniqueMember (A : Class α) (x : α) : Prop :=
  A x ∧ ∀ y, A y → y = x

/-- The contextual condition that `x` is the value of `ι̌ʻA`. -/
def converseIotaValue (A : Class α) (x : α) : Prop :=
  A = singleton x

/-- Equality of the two contextual descriptions in PM I ✱52·17.  Both must
have the same existing unique value; no total description term is created. -/
def descriptionsAgree (P Q : α → Prop) : Prop :=
  ∃ x, P x ∧ Q x ∧
    (∀ y, P y → y = x) ∧ (∀ y, Q y → y = x)

/-- Exact contextual-description equality PM I ✱52·17. -/
theorem star_52_17 (A : Class α) :
    unitClasses α A ↔
      descriptionsAgree (converseIotaValue A) (uniqueMember A) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, rfl, ⟨rfl, fun y hy => hy⟩, ?_, ?_⟩
    · intro y equality
      have atY : singleton x y := by
        rw [equality]
        rfl
      exact atY
    · intro y member
      exact (member.2 x rfl).symm
  · rintro ⟨x, _, member, _, _⟩
    exact ⟨x, by
      funext y
      apply propext
      exact ⟨fun hy => member.2 y hy, fun hy => hy ▸ member.1⟩⟩

/-- Exact existence assertion PM I ✱52·171. -/
theorem star_52_171 (A : Class α) :
    unitClasses α A ↔ ∃ x, uniqueMember A x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl, fun y hy => hy⟩
  · rintro ⟨x, member, unique⟩
    exact ⟨x, by
      funext y
      apply propext
      exact ⟨fun hy => unique y hy, fun hy => hy ▸ member⟩⟩

/-- Exact contextual singleton reconstruction PM I ✱52·172. -/
theorem star_52_172 (A : Class α) :
    unitClasses α A ↔ ∃ x, uniqueMember A x ∧ singleton x = A := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, ⟨rfl, fun y hy => hy⟩, rfl⟩
  · rintro ⟨x, _, equality⟩
    exact ⟨x, equality.symm⟩

/-- Exact contextual membership assertion PM I ✱52·173. -/
theorem star_52_173 (A : Class α) :
    unitClasses α A ↔ ∃ x, uniqueMember A x ∧ A x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, ⟨rfl, fun y hy => hy⟩, rfl⟩
  · rintro ⟨x, ⟨member, unique⟩, _⟩
    exact ⟨x, by
      funext y
      apply propext
      exact ⟨fun hy => unique y hy, fun hy => hy ▸ member⟩⟩

/-- Exact witness-first formulation PM I ✱52·18. -/
theorem star_52_18 (A : Class α) :
    unitClasses α A ↔ ∃ x, A x ∧ ∀ y, A y → y = x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl, fun y hy => hy⟩
  · rintro ⟨x, member, unique⟩
    refine ⟨x, ?_⟩
    funext y
    apply propext
    exact ⟨fun hy => unique y hy, fun hy => hy ▸ member⟩

/-- Exact negated-unit characterization PM I ✱52·181. -/
theorem star_52_181 (A : Class α) :
    ¬ unitClasses α A ↔ ∀ x, A x → ∃ y, A y ∧ y ≠ x := by
  classical
  constructor
  · intro notUnit x memberX
    apply Classical.byContradiction
    intro noOther
    apply notUnit
    apply (star_52_16 A).2
    refine ⟨⟨x, memberX⟩, ?_⟩
    intro y z memberY memberZ
    have yx : y = x := by
      apply Classical.byContradiction
      intro unequal
      exact noOther ⟨y, memberY, unequal⟩
    have zx : z = x := by
      apply Classical.byContradiction
      intro unequal
      exact noOther ⟨z, memberZ, unequal⟩
    exact yx.trans zx.symm
  · intro alternative
    rintro ⟨x, rfl⟩
    obtain ⟨y, memberY, unequal⟩ := alternative x rfl
    exact unequal memberY

/-- `Cls` at the fixed element type: every well-typed class predicate. -/
def classes (α : Sort u) : Class (Class α) := fun _ => True

/-- Exact type-relative inclusion PM I ✱52·2. -/
theorem star_52_2 :
    ∀ A, unitClasses α A → classes α A := by
  intro A _
  trivial

/-- Exact null-class exclusion PM I ✱52·21. -/
theorem star_52_21 :
    ¬ unitClasses α (fun _ => False) := by
  rintro ⟨x, equality⟩
  have member : singleton x x := rfl
  rw [← equality] at member
  exact member

end PM.Architecture.Star52NextKernel
