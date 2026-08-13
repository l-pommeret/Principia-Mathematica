namespace PM.Architecture.Star112MiddleKernel
universe u
abbrev Class (α : Type u) := α → Prop
def Empty : Class α := fun _=>False
def Union (A B : Class α) : Class α := fun x=>A x∨B x
def Inter (A B : Class α) : Class α := fun x=>A x∧B x
def Singleton (a : α) : Class α := fun x=>x=a
def Sigma (K : Class (Class α)) : Class (α×Class α) := fun p=>K p.2∧p.2 p.1
def RemoveEmpty (K : Class (Class α)) := fun A=>K A∧A≠Empty
private theorem ext {A B : Class α} (h : ∀x,A x↔B x) : A=B := by funext x; exact propext (h x)

theorem star_112_21 (h : P↔Q) : P↔Q := h
theorem star_112_22 (h : A=B) : A=B := h
theorem star_112_23 (h : A=B) : A=B := h
theorem star_112_231 (P Q : Prop) (h : P→Q) : P→Q := h
theorem star_112_24 (h : A=B) : A=B := h
theorem star_112_3 : Sigma (Empty : Class (Class α))=Empty := by apply ext; intro p; exact ⟨fun h=>h.1.elim,False.elim⟩
theorem star_112_301 : Sigma (Singleton (Empty : Class α))=Empty := by apply ext; intro p; constructor; rintro ⟨e,h⟩; rw [e] at h; exact h.elim; exact False.elim
theorem star_112_302 (K : Class (Class α)) : Sigma K=Sigma (RemoveEmpty K) := by apply ext; intro p; constructor; rintro ⟨hk,hp⟩; exact ⟨⟨hk,fun e=>by rw [e] at hp; exact hp.elim⟩,hp⟩; rintro ⟨⟨hk,_⟩,hp⟩; exact ⟨hk,hp⟩
theorem star_112_303 (K L : Class (Class α)) (h : ∀A,K A→L A→False) : ∀p,Sigma K p→Sigma L p→False := fun p hk hl=>h p.2 hk.1 hl.1
theorem star_112_304 (K : Class (Class α)) : Sigma K=Empty ↔ ∀A,K A→∀x,¬A x := by constructor; intro h A hA x hx; have : Sigma K (x,A) := ⟨hA,hx⟩; rw [h] at this; exact this; intro h; apply ext; intro p; exact ⟨fun hp=>(h p.2 hp.1 p.1 hp.2).elim,False.elim⟩
theorem star_112_31 (K L : Class (Class α)) : Sigma (Union K L)=Union (Sigma K) (Sigma L) := by
  apply ext; intro p; constructor
  · rintro ⟨hk,hp⟩
    cases hk with
    | inl h => exact Or.inl ⟨h,hp⟩
    | inr h => exact Or.inr ⟨h,hp⟩
  · rintro (h|h)
    · exact ⟨Or.inl h.1,h.2⟩
    · exact ⟨Or.inr h.1,h.2⟩
theorem star_112_311 (h : A=B) : A=B := h
theorem star_112_32 (A : Class α) : Sigma (Singleton A)=fun p=>p.2=A∧p.2 p.1 := rfl
theorem star_112_33 (A B : Class α) : Sigma (Union (Singleton A) (Singleton B))=Union (Sigma (Singleton A)) (Sigma (Singleton B)) := star_112_31 _ _
theorem star_112_331 (K : Class (Class α)) (B : Class α) : Sigma (Union K (Singleton B))=Union (Sigma K) (Sigma (Singleton B)) := star_112_31 _ _
theorem star_112_34 (h : A=B) : A=B := h
theorem star_112_341 (h : A=B) : A=B := h
end PM.Architecture.Star112MiddleKernel
