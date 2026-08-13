namespace PM.Architecture.Star233AnalyticArchitecture

abbrev Class (α : Sort u) := α → Prop
abbrev PFunction (α : Type u) (β : Type v) := α → Option β
def compose (f : PFunction β γ) (g : PFunction α β) : PFunction α γ :=
  fun x => (g x).bind f
def Graph (f : PFunction α β) (x : α) (y : β) := f x = some y
def ExistsValue (f : PFunction α β) (x : α) := ∃ y, Graph f x y
def UniqueValue (f : PFunction α β) (x : α) (y : β) :=
  Graph f x y ∧ ∀ z, Graph f x z → z = y

theorem graph_functional : Graph f x y → Graph f x z → y = z := by
  intro hy hz; exact Option.some.inj (hy.symm.trans hz)
theorem exists_compose_iff : ExistsValue (compose f g) x ↔
    ∃ y z, Graph g x y ∧ Graph f y z := by
  cases h : g x with
  | none => simp [ExistsValue, Graph, compose, h]
  | some y => simp [ExistsValue, Graph, compose, h]

def Connex (P : α → α → Prop) := ∀ x y, x = y ∨ P x y ∨ P y x
def Asymmetric (P : α → α → Prop) := ∀ {x y}, P x y → ¬ P y x
def Greatest (P : α → α → Prop) (A : Class α) (y : α) :=
  A y ∧ ∀ z, A z → z = y ∨ P z y

theorem greatest_unique (ha : Asymmetric P) : Greatest P A x → Greatest P A y → x = y := by
  rintro ⟨hx, gx⟩ ⟨hy, gy⟩
  rcases gx y hy with rfl | hyx
  · rfl
  · rcases gy x hx with rfl | hxy
    · rfl
    · exact False.elim (ha hyx hxy)

def Transitive (P : α → α → Prop) := ∀ {x y z}, P x y → P y z → P x z
def Series (P : α → α → Prop) := Connex P ∧ Asymmetric P ∧ Transitive P
def Deductive (P : α → α → Prop) :=
  ∀ A : Class α, (∃ x, A x) → ∃ y, Greatest P A y
def upperSegment (P : α → α → Prop) (y : α) : Class α := fun z => P y z
def image (P : α → α → Prop) (A : Class α) : Class α :=
  fun y => ∃ x, A x ∧ P x y

theorem upperSegment_injective (hs : Series P) :
    upperSegment P x = upperSegment P y → x = y := by
  intro equality
  rcases hs.1 x y with rfl | hxy | hyx
  · rfl
  · have : P y y := Eq.mp (congrFun equality y) hxy
    exact False.elim (hs.2.1 this this)
  · have : P x x := Eq.mp (congrFun equality.symm x) hyx
    exact False.elim (hs.2.1 this this)

theorem deductive_greatest (ha : Asymmetric P) (hd : Deductive P) (hA : ∃ x, A x) :
    ∃ y, Greatest P A y ∧ ∀ z, Greatest P A z → z = y := by
  obtain ⟨y,hy⟩ := hd A hA
  exact ⟨y,hy, fun z hz => greatest_unique ha hz hy⟩

end PM.Architecture.Star233AnalyticArchitecture
