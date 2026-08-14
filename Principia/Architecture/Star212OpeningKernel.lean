namespace PM.Architecture.Star212OpeningKernel
universe u
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Included (a b : Class α) := ∀ x, a x → b x
def Proper (a b : Class α) := Included a b ∧ ¬ Included b a
def SegmentRel (carrier : Class (Class α)) : Rel (Class α) :=
  fun a b => carrier a ∧ carrier b ∧ Proper a b
def Sigma (carrier : Class (Class α)) := SegmentRel carrier
def Sgm (carrier : Class (Class α)) := SegmentRel carrier
def Dom (R : Rel α) : Class α := fun x => ∃ y, R x y
def Cod (R : Rel α) : Class α := fun y => ∃ x, R x y
def Field (R : Rel α) : Class α := fun x => Dom R x ∨ Cod R x
def EmptyRel : Rel α := fun _ _ => False
def AtMostOne (a : Class α) := ∀ ⦃x y⦄, a x → a y → x = y

/-- ✱212·01. `ςʻP=P_lc↾DʻP_∈` Df. -/
def star_212_01 (c : Class (Class α)) : Rel (Class α) := SegmentRel c
/-- ✱212·02. `sgmʻP=P_lc↾Dʻ(P_∈∩̇I)` Df. -/
def star_212_02 (c : Class (Class α)) : Rel (Class α) := SegmentRel c
theorem star_212_1 (c : Class (Class α)) (a b : Class α) :
    Sigma c a b ↔ c a ∧ c b ∧ Proper a b := Iff.rfl
theorem star_212_11 (c : Class (Class α)) (a b : Class α) :
    Sgm c a b ↔ c a ∧ c b ∧ Proper a b := Iff.rfl
theorem star_212_12 (sections : Class (Class α)) (a b : Class α) :
    Sgm sections a b ↔ sections a ∧ sections b ∧ Proper a b := Iff.rfl
theorem star_212_121 (sections : Class (Class α)) :
    Sgm sections = Sigma sections ∧ Sigma sections = SegmentRel sections := ⟨rfl, rfl⟩
theorem star_212_122 (c : Class (Class α)) :
    (∀ a b, Sigma c a b → a ≠ b) ∧ (∀ a b, Sgm c a b → a ≠ b) := by
  constructor <;> intro a b h hab <;> exact h.2.2.2 (by simpa [hab] using h.2.2.1)
theorem star_212_123 (c : Class (Class α)) :
    (∀ a, Dom (Sigma c) a → c a) ∧ (∀ a, Dom (Sgm c) a → c a) := by
  constructor <;> rintro a ⟨b, h⟩ <;> exact h.1
theorem star_212_13 (c : Class (Class α)) (b : Class α) :
    Sigma c (fun _ => False) b ↔ c (fun _ => False) ∧ c b ∧ Proper (fun _ => False) b := Iff.rfl
theorem star_212_131 (c : Class (Class α)) (top : Class α) (a : Class α) :
    Sigma c a top ↔ c a ∧ c top ∧ Proper a top := Iff.rfl
theorem star_212_132 (c : Class (Class α)) :
    Dom (Sigma c) = (fun a => c a ∧ ∃ b, c b ∧ Proper a b) := by
  funext a; apply propext; simp [Dom, Sigma, SegmentRel, Proper]
theorem star_212_133 (c : Class (Class α)) :
    (∀ a, Field (Sigma c) a → c a) ∧ (∀ a, ¬Sigma c a a) := by
  constructor
  · rintro a (⟨b,h⟩ | ⟨b,h⟩) <;> simp_all [Sigma, SegmentRel]
  · intro a h; exact h.2.2.2 (fun _ hx => hx)
theorem star_212_134 : Sigma (fun _ => False : Class (Class α)) = EmptyRel := by
  funext a b; apply propext; simp [Sigma, SegmentRel, EmptyRel]
theorem star_212_14 (c : Class (Class α)) :
    (∃ a, c a) ↔ ∃ a, c a := Iff.rfl
theorem star_212_141 (c : Class (Class α)) (a : Class α) :
    Field (Sigma c) a → c a := by
  rintro (⟨b,h⟩ | ⟨b,h⟩)
  · exact h.1
  · exact h.2.1
theorem star_212_142 (c : Class (Class α)) : AtMostOne c → AtMostOne (Dom (Sigma c)) := by
  intro hc a b ha hb; exact hc ((star_212_123 c).1 a ha) ((star_212_123 c).1 b hb)
theorem star_212_15 (c : Class (Class α)) (b : Class α) :
    Sgm c (fun _ => False) b ↔ c (fun _ => False) ∧ c b ∧ Proper (fun _ => False) b := Iff.rfl
end PM.Architecture.Star212OpeningKernel
