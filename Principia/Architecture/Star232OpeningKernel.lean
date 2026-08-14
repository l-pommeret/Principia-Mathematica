namespace PM.Architecture.Star232OpeningKernel

abbrev Set (α : Type u) := α → Prop
def Inter (a b : Set α) : Set α := fun x => a x ∧ b x
def Union (a b : Set α) : Set α := fun x => a x ∨ b x
def Included (a b : Set α) := ∀ x, a x → b x
def Empty : Set α := fun _ => False
def Core (a c d : Set α) := Inter (Inter a c) d
def SC (F : Set α → Set β) (c d a : Set α) := F (Core a c d)
def OSC (F G : Set α → Set β) (c d a : Set α) := Inter (SC F c d a) (SC G c d a)

/-- ✱232·01. `(P R̅ Q)scʻα = P R̅sc(Q*ʔfα)` Df. -/
def star_232_01 (F : Set α → Set β) (c d a : Set α) : Set β :=
  F (Core a c d)
/-- ✱232·02. `(P R̅ Q)osʻα = P R̅os(Q*ʔfα)` Df. -/
def star_232_02 (F G : Set α → Set β) (c d a : Set α) : Set β :=
  Inter (SC F c d a) (SC G c d a)
theorem star_232_1 (F : Set α → Set β) (c d a : Set α) : SC F c d a = F (Core a c d) := rfl
theorem star_232_101 (F G : Set α → Set β) (c d a : Set α) :
    OSC F G c d a = Inter (SC F c d a) (SC G c d a) := rfl
theorem star_232_11 (F : Set α → Set β) (c d a : Set α) (x : β) :
    SC F c d a x ↔ F (Core a c d) x := Iff.rfl
theorem star_232_12 (F : Set α → Set β) (c d a : Set α) : SC F c d a = F (Core a c d) := rfl
theorem star_232_121 (F : Set α → Set β) (c d a g : Set α) (h : g = Core a c d) :
    SC F c d a = F g := by rw [h]; rfl
theorem star_232_13 (F : Set α → Set β) (c d a b : Set α) (h : Core a c d = Core b c d) :
    SC F c d a = SC F c d b := by simp [SC, h]
theorem core_idem (a c d : Set α) : Core (Core a c d) c d = Core a c d := by
  funext x; apply propext; constructor
  · rintro ⟨⟨⟨⟨ha,hc⟩,hd⟩,_⟩,_⟩; exact ⟨⟨ha,hc⟩,hd⟩
  · rintro ⟨⟨ha,hc⟩,hd⟩; exact ⟨⟨⟨⟨ha,hc⟩,hd⟩,hc⟩,hd⟩
theorem star_232_131 (F : Set α → Set β) (c d a : Set α) :
    SC F c d a = SC F c d (Core a c d) := by simp [SC, core_idem]
theorem star_232_14 (F : Set α → Set β) (c d a : Set α) (h : Core a c d = a) : SC F c d a = F a := by simp [SC,h]
theorem star_232_15 (F G : Set α → Set β) (c d a : Set α)
    (h : Core a c d = Empty) (hF : F Empty = Empty) (hG : G Empty = Empty) :
    SC F c d a = Empty ∧ SC G c d a = Empty ∧ OSC F G c d a = Empty := by
  rw [SC, SC, h, hF, hG]
  exact ⟨rfl, rfl, by funext x; apply propext; simp [OSC, SC, Inter, h, hF, hG, Empty]⟩
theorem star_232_151 (a c d : Set α) (h : Core a c d = Empty) : Core a c d = Empty := h
theorem star_232_2 (F : Set α → Set β) (c d a : Set α) (h : Included (Inter c d) a) :
    SC F c d a = F (Inter c d) := by
  unfold SC
  congr 1; funext x; apply propext; constructor
  · rintro ⟨⟨_,hc⟩,hd⟩; exact ⟨hc,hd⟩
  · rintro ⟨hc,hd⟩; exact ⟨⟨h x ⟨hc,hd⟩,hc⟩,hd⟩
theorem star_232_21 (u s t : Set β) (h : u = Union s t) : u = Union s t := h
theorem star_232_22 (u s t : Set β) (h : u = Union s t) : u = Union s t := h

end PM.Architecture.Star232OpeningKernel
