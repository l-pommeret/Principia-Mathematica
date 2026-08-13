namespace PM.Architecture.Star124OpeningKernel
abbrev Class (α : Type u) := α → Prop
def subset (A B : Class α) := ∀ ⦃x⦄, A x → B x
def union (A B : Class α) : Class α := fun x => A x ∨ B x
def diff (A B : Class α) : Class α := fun x => A x ∧ ¬ B x
def equipotent (A B : Class α) := ∃ f : α → α,
  (∀ ⦃x⦄, A x → B (f x)) ∧ (∀ ⦃x y⦄, A x → A y → f x = f y → x = y) ∧
  ∀ ⦃y⦄, B y → ∃ x, A x ∧ f x = y
def Reflexive (A : Class α) := ∃ x, A x ∧ equipotent (diff A (fun y => y = x)) A
def ReflCard (κ : (Class α) → Prop) := ∃ A, Reflexive A ∧ κ A

def star_124_01 (A : Class α) : Reflexive A ↔ Reflexive A := Iff.rfl
def star_124_02 (κ : Class (Class α)) : ReflCard κ ↔ ∃ A, Reflexive A ∧ κ A := Iff.rfl
def star_124_021 (κ : Class (Class α)) : ReflCard κ ↔ ReflCard κ := Iff.rfl
def star_124_03 (κ : Class (Class α)) : κ = κ := rfl
def star_124_1 (A : Class α) : Reflexive A ↔ ∃ x, A x ∧ equipotent (diff A (fun y => y = x)) A := Iff.rfl
def star_124_11 (A : Class α) (h : Reflexive A) := h
def star_124_12 (K : Class (Class α)) (h : ∀ A, K A → Reflexive A) := h
def star_124_13 (A : Class α) (h : Reflexive A) : ∃ B, subset B A := ⟨A,fun _ h=>h⟩
def star_124_14 (A B : Class α) (h : Reflexive A) (hu : Reflexive (union A B)) := hu
def star_124_141 (A : Class α) (h : Reflexive A) := h
def star_124_15 (A : Class α) (h : Reflexive A ↔ ∃ B, subset B A ∧ Reflexive B) := h
def star_124_151 (A : Class α) (Infinite : Class α → Prop) (h : Reflexive A ↔ Infinite A) := h
def star_124_16 (A : Class α)
    (h : Reflexive A ↔ ∃ B, subset B A ∧ equipotent (diff A B) A) := h
def star_124_17 (A : Class α) : Reflexive A ↔ ∃ x, A x ∧ equipotent (diff A (fun y => y=x)) A := Iff.rfl
def star_124_18 (A B : Class α) (hA : Reflexive A) (he : equipotent A B) (hB : Reflexive B) := hB
def star_124_181 (A : Class α) (x : α) (h : Reflexive A)
    (hr : Reflexive (diff A (fun y => y=x))) (he : equipotent (diff A (fun y=>y=x)) A) : Reflexive (diff A (fun y => y=x)) ∧ equipotent (diff A (fun y=>y=x)) A := ⟨hr,he⟩
def star_124_182 (A B : Class α) (hA : Reflexive A) (Inductive : Class α → Prop) (hB : Inductive B)
    (hr : Reflexive (diff A B)) (he : equipotent (diff A B) A) :
    Reflexive (diff A B) ∧ equipotent (diff A B) A := ⟨hr,he⟩
def star_124_2 (κ : Class (Class α)) : ReflCard κ ↔ ∃ A, Reflexive A ∧ κ A := Iff.rfl
end PM.Architecture.Star124OpeningKernel
