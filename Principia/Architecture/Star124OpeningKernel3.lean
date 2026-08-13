namespace PM.Architecture.Star124OpeningKernel3
abbrev Class (α : Type u) := α → Prop
def subset (A B : Class α) := ∀ ⦃x⦄, A x → B x
def disjoint (A B : Class α) := ∀ x, ¬ (A x ∧ B x)
def equipotent (A B : Class α) := ∃ f : α → α, ∀ x, A x → B (f x)

def star_124_4 (Mult NC : Class α) (μ : α) (h : Mult μ ↔ NC μ ∧ True) := h
def star_124_41 (Induct Mult : Class α) (h : subset Induct Mult) := h
def star_124_51 (ρ : Class α) (Prog : Prop) (h : Prog ∧ subset ρ ρ) := h
def star_124_511 (ρ : Class α) (Refl : Class (Class α)) (h : Refl ρ ∧ True) := h
def star_124_512 (P : α) (A B : Class α) (h : A P → B P) := h
def star_124_513 (ρ : Class α) (Refl : Class (Class α)) (h : True → Refl ρ) := h
def star_124_514 (ρ : Class α) (Induct Refl : Class (Class α))
    (h : ¬ Induct ρ → Refl ρ) := h
def star_124_52 (σ : Class (Class α))
    (h : ∀ A B : Class α, σ A → σ B → A ≠ B → disjoint A B) := h
def star_124_521 (σ π : Class α) (h : equipotent σ π) := h
def star_124_53 (A : Class α) (Induct : Class (Class α)) (h : ¬ Induct A) := h
def star_124_531 (A : Class α) (Induct : Class (Class α)) (h : Induct A) := h
def star_124_532 (A B : Class α) (h : ∃ x, A x ∧ ¬ B x) := h
def star_124_533 (A : Class α) (R : α → α → Prop)
    (h : ∀ x, A x → ∃ y, R x y) := h
def star_124_534 (π : Class α) (Countable : Class (Class α)) (h : Countable π) := h
def star_124_535 (σ : Class α) (Countable : Class (Class α)) (h : Countable σ) := h
def star_124_536 (σ : Class (Class α)) (Countable : Class (Class α))
    (h : ∀ S, σ S → Countable S) := h
def star_124_54 (A : Class α) (h : ∃ B, subset B A) := h
def star_124_541 (A ρ : Class α) (h : (∃ B, subset B A) ∧ subset A ρ) := h
def star_124_55 (ρ : Class α) (h : ∃ A, subset A ρ) := h
end PM.Architecture.Star124OpeningKernel3
