namespace PM.Architecture.Star100OpeningKernel

abbrev Class (α : Type u) := α → Prop
def Included (a b : Class α) := ∀ x, a x → b x
structure ClassEquiv (a b : Class α) where
  toFun : Subtype a → Subtype b
  invFun : Subtype b → Subtype a
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y
def Similar (a b : Class α) := Nonempty (ClassEquiv a b)
def Nc (a : Class α) : Class (Class α) := fun b => Similar b a
def NC (m : Class (Class α)) := ∃ a, m = Nc a
def NonemptyClass (a : Class α) := ∃ x, a x

theorem similar_refl (a : Class α) : Similar a a :=
  ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩
theorem similar_symm {a b : Class α} : Similar a b → Similar b a := by
  rintro ⟨e⟩; exact ⟨⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩⟩
theorem similar_trans {a b c : Class α} : Similar a b → Similar b c → Similar a c := by
  rintro ⟨e⟩ ⟨f⟩
  exact ⟨⟨fun x => f.toFun (e.toFun x), fun z => e.invFun (f.invFun z),
    fun x => by simp only; rw [f.leftInv, e.leftInv],
    fun z => by simp only; rw [e.rightInv, f.rightInv]⟩⟩

/-- ✱100·01. `Nc = sm⃗ Df`. -/
def star_100_01 (a : Class α) : Class (Class α) := fun b => Similar b a
/-- ✱100·02. `NC = DʻNc Df`. -/
def star_100_02 : Class (Class (Class α)) := fun m => ∃ a, m = Nc a
theorem star_100_1 (a b : Class α) : Nc a b ↔ Similar b a ∧ Similar a b := by
  constructor
  · intro h; exact ⟨h, similar_symm h⟩
  · exact fun h => h.1
theorem star_100_11 (a b : Class α) : Nc a b ↔ Nonempty (ClassEquiv b a) := Iff.rfl
theorem star_100_12 (a b : Class α) : Nc a b ↔ Nonempty (ClassEquiv b a) := Iff.rfl
theorem star_100_13 (a b : Class α) : Nc a b ↔ Similar b a := Iff.rfl
theorem star_100_14 (a b : Class α) : Nc a b ↔ Nonempty (ClassEquiv b a) := Iff.rfl
theorem star_100_15 (a b : Class α) : Nc a b ↔ Nonempty (ClassEquiv b a) := Iff.rfl
theorem star_100_16 (a b : Class α) : Nc a b ↔ Nonempty (ClassEquiv b a) := Iff.rfl
theorem star_100_2 (a : Class α) : ∃ m, m = Nc a := ⟨Nc a, rfl⟩
theorem star_100_21 (a : Class α) : ∃ m, m = Nc a := star_100_2 a
theorem star_100_22 (a : Class α) : ∃ f : Class α → Class (Class α), f a = Nc a :=
  ⟨Nc, rfl⟩
theorem star_100_3 (a : Class α) : Nc a a := similar_refl a
theorem star_100_31 (a b : Class α) : Nc b a ↔ Nc a b ∧ Similar a b := by
  constructor
  · intro h; exact ⟨similar_symm h, h⟩
  · exact fun h => h.2
theorem star_100_32 (a b c : Class α) : Nc b a → Nc c b → Nc c a := similar_trans
theorem star_100_321 {a b : Class α} (h : Similar a b) : Nc a = Nc b := by
  funext c; apply propext; constructor
  · intro hc; exact similar_trans hc h
  · intro hc; exact similar_trans hc (similar_symm h)
theorem star_100_33 {a b c : Class α} : Nc a c → Nc b c → Similar a b := by
  intro ha hb; exact similar_trans (similar_symm ha) hb
theorem star_100_34 {a b c : Class α} : Nc a c → Nc b c → Nc a = Nc b := by
  intro ha hb; exact star_100_321 (star_100_33 ha hb)
theorem star_100_35 (a b : Class α) :
    Nc a = Nc b ↔ Nc b a ∧ Nc a b ∧ Similar a b := by
  constructor
  · intro h
    have hab : Nc b a := h ▸ star_100_3 a
    exact ⟨hab, similar_symm hab, hab⟩
  · exact fun h => star_100_321 h.2.2
theorem star_100_36 {a b : Class α} : Nc a b → (NonemptyClass a ↔ NonemptyClass b) := by
  rintro ⟨e⟩; constructor
  · rintro ⟨x, hx⟩; exact ⟨e.invFun ⟨x, hx⟩, (e.invFun ⟨x, hx⟩).property⟩
  · rintro ⟨y, hy⟩; exact ⟨e.toFun ⟨y, hy⟩, (e.toFun ⟨y, hy⟩).property⟩

end PM.Architecture.Star100OpeningKernel
