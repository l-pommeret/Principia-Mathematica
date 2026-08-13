namespace PM.Architecture.Star124OpeningKernel4
abbrev Class (α : Type u) := α → Prop
def complement (A : Class α) : Class α := fun x => ¬ A x
def diff (A B : Class α) : Class α := fun x => A x ∧ ¬ B x

def star_124_56 (Induct Refl : Class α)
    (h₁ : complement Induct = Refl)
    (h₂ : diff (fun _ => True) Induct = Refl) :
    complement Induct = Refl ∧ diff (fun _ => True) Induct = Refl := ⟨h₁,h₂⟩
def star_124_57 (μ : α) (Refl : Class α) (h : Refl μ) := h
def star_124_58 (All Induct Refl : Class α)
    (h : (∀ μ, Refl μ → Refl μ) → diff All Induct = Refl) := h
def star_124_6 (ρ : α) (Induct Refl : Class α) (Cl : α → α)
    (h : ¬ Induct ρ ↔ Refl (Cl (Cl ρ))) := h
def star_124_61 (ρ : α) (Refl : Class α) (Cl : α → α)
    (h : Refl ρ ↔ Refl (Cl ρ) ∧ Refl (Cl (Cl ρ))) := h
end PM.Architecture.Star124OpeningKernel4
