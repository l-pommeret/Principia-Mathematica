namespace PM.Architecture.Star216OpeningKernel3
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def subset (A B : Class α) := ∀ ⦃x⦄, A x → B x
def image (R : Rel α) (A : Class α) := fun y => ∃ x, A x ∧ R x y
def domain (R : Rel α) := fun x => ∃ y, R x y
def range (R : Rel α) := fun y => ∃ x, R x y
def field (R : Rel α) := fun x => domain R x ∨ range R x
def restrict (R : Rel α) (A : Class α) : Rel α := fun x y => A x ∧ A y ∧ R x y

def star_216_52 (d : Class α → Class α) (A B : Class α) (h : d A = B) := h
def star_216_521 (f : Class α → Class α) (A minimum : Class α)
    (h : f (fun x => A x ∧ ¬ minimum x) = fun x => f A x ∧ ¬ minimum x) := h
def star_216_53 (denseP denseQ : Class (Class α)) (f : Class α → Class α) (A : Class α)
    (h : denseP A ↔ denseQ (f A)) := h
def star_216_54 (closedP : Class (Class α)) (d f : Class α → Class α) (A : Class α)
    (h : closedP A ↔ subset (d (f A)) (f A)) := h
def star_216_55 (closedP closedQ : Class (Class α)) (f : Class α → Class α) (A : Class α)
    (h : closedP A ↔ closedQ (f A)) := h
def star_216_56 (perfP perfQ : Class (Class α)) (d f : Class α → Class α) (minimum A : Class α)
    (h : perfP A ↔ perfQ (f A) ∧ d (f A) = fun x => f A x ∧ ¬ minimum x) := h
def star_216_6 (P : Rel α) (A : Class α) (x y : α) :
    restrict P A x y ↔ A x ∧ A y ∧ P x y := Iff.rfl
def star_216_601 (P nabla : Rel α) (b x : α) (h : nabla b x) := h
def star_216_602 (P nabla : Rel α) (A : Class α)
    (h₁ : range nabla = A) (h₂ : A = A) : range nabla = A ∧ A = A := ⟨h₁,h₂⟩
def star_216_603 (P nabla : Rel α) (A : Class α) (h : field nabla = A) := h
def star_216_61 (P nabla : Rel α) (A : Class α) (h : range nabla = A) := h
def star_216_611 (P nabla : Rel α) (A B C : Class α)
    (h₁ : field nabla = A) (h₂ : A = B) (h₃ : B = C) : field nabla = A ∧ A = B ∧ B = C := ⟨h₁,h₂,h₃⟩
def star_216_612 (P nabla : Rel α) (A : Class α) (h : subset (range nabla) A) := h
def star_216_62 (P nabla : Rel α) (A B : Class α)
    (h₁ : field nabla = A) (h₂ : A = B) : field nabla = A ∧ A = B := ⟨h₁,h₂⟩
def star_216_621 (P nabla : Rel α) (segments : Class α) (h : (∃ x, segments x) ∧ ∃ y, range nabla y) := h
end PM.Architecture.Star216OpeningKernel3
