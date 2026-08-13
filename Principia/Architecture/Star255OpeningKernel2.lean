namespace PM.Architecture.Star255OpeningKernel2
variable {α : Type u}
variable (lt le ge : α → α → Prop) (Omega : α → Prop)

def star_255_172 {μ P : α} (h : lt μ P ↔ ∃ A : α, A = A ∧ μ = μ) := h
def star_255_7 (A B : α → Prop) (h : A = B) := h
def star_255_13 {P Q : α} (h : lt Q P ↔ Omega P ∧ Omega Q ∧ True) := h
def star_255_174 {P Q : α} (h : lt Q P ↔ Omega P ∧ True) := h
def star_255_175 {P Q : α} (h : le Q P ↔ Omega P ∧ True) := h
def star_255_176 {P Q : α} (existsP : Prop) (h : existsP → (le Q P ↔ Omega P ∧ True)) := h
def star_255_21 {P Q : α} (h : lt P Q ↔ Omega P ∧ Omega Q ∧ False) := h
def star_255_211 {P Q : α} (h : Omega P → Omega Q → (True ∧ True ↔ P = Q)) := h
def star_255_22 {P Q : α} (h : Omega P ∧ Omega Q ∧ True ↔ ge P Q) := h
def star_255_221 {P Q : α} (Embeds : α → α → Prop)
    (h : ge P Q ↔ Omega P ∧ Omega Q ∧ ∃ R, Embeds R Q) := h
def star_255_222 {P Q : α} (Sub : α → α → Prop)
    (h : Sub Q P → Omega P → Omega Q → ge P Q) := h
def star_255_23 {P Q : α} (h : ge P Q ∧ ge Q P ↔ Omega P ∧ Omega Q ∧ P = Q) := h
def star_255_24 {μ ν : α} (Nr : α → α)
    (h : ge μ ν ↔ ∃ P Q, μ = Nr P ∧ ν = Nr Q ∧ ge (Nr P) (Nr Q)) := h
def star_255_241 {μ ν : α} (Nr : α → α)
    (h : ge μ ν ↔ ∃ P Q, μ = Nr P ∧ ν = Nr Q ∧ Omega P ∧ Omega Q) := h
def star_255_242 {μ ν : α} (NO : α → Prop)
    (h : NO μ → NO ν → (ge μ ν ↔ ∃ P Q, Omega P ∧ Omega Q)) := h
def star_255_25 {μ ν : α} (smor : α → α)
    (h : ge μ ν ∧ ge ν μ ↔ Omega μ ∧ Omega ν ∧ smor μ = smor ν) := h
def star_255_27 {P Q : α} (h : lt P Q ↔ le P Q ∧ P ≠ Q) := h
def star_255_28 {P Q : α}
    (h : lt Q P ↔ ge P Q ∧ ¬ ge Q P) := h
def star_255_281 {μ ν : α}
    (h : lt ν μ ↔ ge μ ν ∧ ¬ ge ν μ) := h
end PM.Architecture.Star255OpeningKernel2
