namespace PM.Architecture.Star92OpeningKernel
universe u
abbrev Rel (α : Type u) := α → α → Prop
abbrev Set (α : Type u) := α → Prop
def Dom (R : Rel α) : Set α := fun x => ∃y,R x y
def Cod (R : Rel α) : Set α := fun y => ∃x,R x y
def Inc (A B : Set α) := ∀x,A x→B x
def Converse (R : Rel α) : Rel α := fun x y=>R y x
def RestrictD (R : Rel α) (A : Set α) : Rel α := fun x y=>A x∧R x y
def RestrictC (R : Rel α) (A : Set α) : Rel α := fun x y=>R x y∧A y
def Potid (R Q : Rel α) := Dom Q=Dom R ∧ Cod Q=Cod R

theorem star_92_1 (h : Potid R Q) : Dom Q=Dom R := h.1
theorem star_92_101 (h : Potid R Q) : Cod Q=Cod R := h.2
theorem star_92_102 (h : Potid R Q) : Dom Q=Dom R ∧ Cod Q=Cod R := h
theorem star_92_11 (h₁ : Inc (Cod R) (Dom R)) (h₂ : Potid R Q) : Inc (Cod Q) (Dom R) := by rw [h₂.2]; exact h₁
theorem star_92_112 (h : Potid R Q) : RestrictD Q (Dom R)=RestrictD Q (Dom Q) := by rw [h.1]
theorem star_92_113 (h : Potid R Q) : RestrictC Q (Cod R)=RestrictC Q (Cod Q) := by rw [h.2]
theorem star_92_12 (h₁ : Inc (Cod R) (Dom R)) (h₂ : Potid R Q) : Inc (Cod Q) (Dom Q) := by rw [h₂.1,h₂.2]; exact h₁
theorem star_92_121 (h₁ : Inc (Dom R) (Cod R)) (h₂ : Potid R Q) : Inc (Dom Q) (Cod Q) := by rw [h₂.1,h₂.2]; exact h₁
theorem star_92_13 (hq : Potid R Q) (ht : Potid R T) : Dom Q=Dom T := hq.1.trans ht.1.symm
theorem star_92_131 (hq : Potid R Q) (ht : Potid R T) : Cod Q=Cod T := hq.2.trans ht.2.symm
theorem star_92_132 (hq : Potid R Q) (ht : Potid R T) : Dom Q=Dom T ∧ Cod Q=Cod T := ⟨star_92_13 hq ht,star_92_131 hq ht⟩
theorem star_92_14 (h : Potid R Q) : Dom Q=Dom R := h.1
theorem star_92_141 (h : Potid R Q) : Cod Q=Cod R := h.2
theorem star_92_142 (h : Potid R Q) : Dom Q=Dom R := h.1
theorem star_92_143 (h : Potid R Q) : Cod Q=Cod R := h.2
theorem star_92_144 (hR : Inc (Cod R) (Dom R)) (h : Potid R Q) : Inc (Cod Q) (Dom R) ∧ Inc (Cod Q) (Dom Q) := ⟨star_92_11 hR h,star_92_12 hR h⟩
theorem star_92_145 (hR : Inc (Dom R) (Cod R)) (h : Potid R Q) : Inc (Dom Q) (Cod R) ∧ Inc (Dom Q) (Cod Q) := by rw [h.1,h.2]; exact ⟨hR,hR⟩
theorem star_92_146 (hq : Potid R Q) : RestrictC T (Dom Q)=RestrictC T (Dom R) := by rw [hq.1]
theorem star_92_147 (hq : Potid R Q) : RestrictD T (Cod Q)=RestrictD T (Cod R) := by rw [hq.2]
end PM.Architecture.Star92OpeningKernel
