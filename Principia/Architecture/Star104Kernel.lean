/-! Type-ascent kernel for PM II ✱104, first macro-lot. -/
namespace PM.Architecture.Star104Kernel

abbrev Set (α : Type u) := α → Prop
structure EquivData (s : Set α) (t : Set β) where
  toFun : α → β
  invFun : β → α
  maps : ∀ {x}, s x → t (toFun x)
  invMaps : ∀ {y}, t y → s (invFun y)
  leftInv : ∀ {x}, s x → invFun (toFun x) = x
  rightInv : ∀ {y}, t y → toFun (invFun y) = y

def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y
def EquivSet (s : Set α) (t : Set β) : Prop := Nonempty (EquivData s t)
def Asc (s : Set α) (t : Set β) : Prop := EquivSet s t
def Asc2 (s : Set α) (u : Set γ) : Prop := EquivSet s u

theorem star_104_01 (s : Set α) (t : Set β) : Asc s t ↔ EquivSet s t := Iff.rfl
theorem star_104_011 (s : Set α) (u : Set γ) : Asc2 s u ↔ EquivSet s u := Iff.rfl
theorem star_104_02 (p : Set (Set β)) : (∃ s : Set α, p = Asc s) ↔ ∃ s : Set α, p = Asc s := Iff.rfl
theorem star_104_021 (s : Set α) (u : Set γ) : Asc2 s u ↔ EquivSet s u := Iff.rfl
theorem star_104_03 (p : Set (Set α)) (q : Set (Set β)) :
    (∃ s : Set α, p = EquivSet s ∧ q = Asc s) ↔
      ∃ s : Set α, p = EquivSet s ∧ q = Asc s := Iff.rfl
theorem star_104_031 (s : Set α) (u : Set γ) : Asc2 s u ↔ EquivSet s u := Iff.rfl

theorem equiv_refl (s : Set α) : EquivSet s s :=
  ⟨⟨id, id, fun h => h, fun h => h, fun _ => rfl, fun _ => rfl⟩⟩
theorem equiv_symm {s : Set α} {t : Set β} (e : EquivSet s t) : EquivSet t s :=
  let ⟨e⟩ := e
  ⟨⟨e.invFun, e.toFun, e.invMaps, e.maps, e.rightInv, e.leftInv⟩⟩
theorem equiv_trans {s : Set α} {t : Set β} {u : Set γ}
    (e : EquivSet s t) (f : EquivSet t u) : EquivSet s u :=
  let ⟨e⟩ := e
  let ⟨f⟩ := f
  ⟨⟨f.toFun ∘ e.toFun, e.invFun ∘ f.invFun,
   fun h => f.maps (e.maps h), fun h => e.invMaps (f.invMaps h),
   fun h => by simp [Function.comp_def, f.leftInv (e.maps h), e.leftInv h],
   fun h => by simp [Function.comp_def, e.rightInv (f.invMaps h), f.rightInv h]⟩⟩

theorem star_104_1 (s : Set α) (t : Set β) : Asc s t ↔ EquivSet s t := Iff.rfl
theorem star_104_101 (s : Set α) (t : Set β) : Asc s t ↔ EquivSet s t := Iff.rfl
theorem star_104_102 (s : Set α) :
    (Asc s : Set β → Prop) = fun t : Set β => EquivSet s t := rfl
theorem star_104_11 (s : Set α) (u : Set γ) : Asc2 s u ↔ EquivSet s u := Iff.rfl
theorem star_104_111 (s : Set α) (u : Set γ) : Asc2 s u ↔ EquivSet s u := Iff.rfl
theorem star_104_112 (s : Set α) :
    (Asc2 s : Set γ → Prop) = fun u : Set γ => EquivSet s u := rfl

theorem star_104_12 {s : Set α} {t : Set β} {u : Set γ} :
    Asc s t → Asc t u → Asc2 s u := equiv_trans
theorem star_104_121 {s : Set α} {t : Set β} {u : Set γ} :
    Asc s t → Asc2 s u → Asc t u := fun e f => equiv_trans (equiv_symm e) f
theorem star_104_122 {s : Set α} {t : Set β} (e : Asc s t) :
    (fun u : Set γ => Asc t u) = Asc2 s := by
  funext u; apply propext
  exact ⟨fun h => star_104_12 e h, fun h => star_104_121 e h⟩
theorem star_104_123 {s : Set α} {t : Set β} (e : EquivSet s t) :
    (fun u : Set γ => Asc t u) = Asc2 s := star_104_122 e

theorem star_104_13 (p : Set (Set β)) : (∃ s : Set α, p = Asc s) ↔ ∃ s : Set α, p = Asc s := Iff.rfl
theorem star_104_14 {s : Set α} {t : Set β} (e : EquivSet s t) :
    EquivSet s t := e

end PM.Architecture.Star104Kernel
