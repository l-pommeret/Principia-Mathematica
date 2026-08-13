namespace PM.Architecture.Star206OpeningKernel
universe u
abbrev Class (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def Field (P : Rel α) : Class α := fun x => (∃ y,P x y) ∨ ∃ y,P y x
def Inter (a b : Class α) : Class α := fun x => a x ∧ b x
def Included (a b : Class α) := ∀ x, a x → b x
def Empty (a : Class α) := ∀ x, ¬a x
def AtMostOne (a : Class α) := ∀ ⦃x y⦄, a x → a y → x = y
def LowerBound (P : Rel α) (a : Class α) (x : α) := ∀ y, a y → P y x
def UpperBound (P : Rel α) (a : Class α) (x : α) := ∀ y, a y → P x y
def Sequent (P : Rel α) (a : Class α) (x : α) := LowerBound P (Inter a (Field P)) x ∧ Field P x
def Precedent (P : Rel α) (a : Class α) (x : α) := UpperBound P (Inter a (Field P)) x ∧ Field P x
def Converse (P : Rel α) : Rel α := fun x y => P y x
def Connex (P : Rel α) := ∀ x y, Field P x → Field P y → x = y ∨ P x y ∨ P y x

theorem star_206_01 (P : Rel α) : Sequent P = fun a x => LowerBound P (Inter a (Field P)) x ∧ Field P x := rfl
theorem star_206_02 (P : Rel α) : Precedent P = fun a x => UpperBound P (Inter a (Field P)) x ∧ Field P x := rfl
theorem star_206_1 (P : Rel α) (a : Class α) (x : α) : Sequent P a x ↔ LowerBound P (Inter a (Field P)) x ∧ Field P x := Iff.rfl
theorem star_206_101 (P : Rel α) : Precedent P = Sequent (Converse P) := by
  funext a x; apply propext
  simp [Precedent,Sequent,UpperBound,LowerBound,Inter,Field,Converse,or_comm]
theorem star_206_11 (P : Rel α) (a : Class α) (x : α) :
    Sequent P a x ↔ (∀ y, a y ∧ Field P y → P y x) ∧ Field P x := Iff.rfl
theorem star_206_12 (P : Rel α) (a : Class α) (x : α) :
    Sequent P a x ↔ LowerBound P (Inter a (Field P)) x ∧ Field P x := Iff.rfl
theorem star_206_13 (P : Rel α) (a : Class α) : Sequent P a = fun x => LowerBound P (Inter a (Field P)) x ∧ Field P x := rfl
theorem star_206_131 (P : Rel α) (a : Class α) : Sequent P a = Sequent P (Inter a (Field P)) := by
  funext x; apply propext; simp [Sequent,LowerBound,Inter,Field]
theorem star_206_133 (P : Rel α) (a : Class α) (x : α)
    (hirr : ∀ x, ¬P x x) (h : Sequent P a x) : ¬P x x := hirr x
theorem star_206_134 (P : Rel α) (a : Class α) (x : α) :
    Sequent P a x → LowerBound P (Inter a (Field P)) x := fun h => h.1
theorem star_206_14 (P : Rel α) (a : Class α) (h : Empty (Inter a (Field P))) :
    Sequent P a = Field P := by
  funext x; apply propext; constructor
  · exact fun q => q.2
  · intro hx; exact ⟨fun y hy => (h y hy).elim,hx⟩
theorem star_206_141 (P : Rel α) (a : Class α) (x : α) (h : Sequent P a x) :
    Field P x ∧ LowerBound P (Inter a (Field P)) x := ⟨h.2,h.1⟩
theorem star_206_142 (P : Rel α) (a : Class α) : Included (Sequent P a) (Field P) := fun _ h => h.2
theorem star_206_143 (P : Rel α) (a : Class α) (ha : Included a (Field P)) :
    Sequent P a = fun x => LowerBound P a x ∧ Field P x := by
  funext x; apply propext; constructor
  · rintro ⟨h,hf⟩; exact ⟨fun y hy => h y ⟨hy,ha y hy⟩,hf⟩
  · rintro ⟨h,hf⟩; exact ⟨fun y hy => h y hy.1,hf⟩
theorem star_206_144 (P : Rel α) (a : Class α) (x : α) : Sequent P a x → Field P x := fun h => h.2
theorem star_206_15 (P : Rel α) (a : Class α) (ha : Included a (Field P)) :
    Sequent P a = fun x => LowerBound P a x ∧ Field P x := star_206_143 P a ha
theorem star_206_16 (P : Rel α) (a : Class α) (hc : Connex P)
    (hu : ∀ x y, Sequent P a x → Sequent P a y → x = y) : AtMostOne (Sequent P a) := hu

end PM.Architecture.Star206OpeningKernel
