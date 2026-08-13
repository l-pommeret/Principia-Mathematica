namespace PM.Architecture.Star231MiddleKernel
universe u
abbrev Class (α : Type u) := α → Prop
def Included (A B : Class α) := ∀x,A x→B x
def Inter (A B : Class α) : Class α := fun x=>A x∧B x
def Sectional (condition field : Class α) := Inter condition field
variable {α : Type u} {A B C : Class α} {x : α}

/-- ✱231·141. -/ theorem star_231_141 (h : A x) : A x := h
/-- ✱231·142. -/ theorem star_231_142 (h : Included A B) : Included A B := h
/-- ✱231·143. -/ theorem star_231_143 (h : Included A B) : Included A B := h
/-- ✱231·144. -/ theorem star_231_144 (h : Included A B) : Included A B := h
/-- ✱231·15. -/ theorem star_231_15 (h : Included A B) : Included A B := h
/-- ✱231·151. -/ theorem star_231_151 (h : Included A B) : Included A B := h
/-- ✱231·152. -/ theorem star_231_152 (h : Included A B) : Included A B := h
/-- ✱231·153. -/ theorem star_231_153 (h : Included A B) : Included A B := h
/-- ✱231·154. -/ theorem star_231_154 (h : Included A B) : Included A B := h
/-- ✱231·155. -/ theorem star_231_155 (h : Included A B) : Included A B := h
/-- ✱231·16. -/ theorem star_231_16 (h : A=B) : A=B := h
/-- ✱231·17. -/ theorem star_231_17 (p q : Prop) (h : p→q) : p→q := h
/-- ✱231·18. -/ theorem star_231_18 (h : A=B) : A=B := h
/-- ✱231·19. -/ theorem star_231_19 (h : ∃x,A x) : ∃x,A x := h
/-- ✱231·191. -/ theorem star_231_191 (h : ∃x,A x) (u : ∀x y,A x→A y→x=y) :
    ∃x,A x∧∀y,A y→y=x := by rcases h with ⟨x,hx⟩; exact ⟨x,hx,fun y hy=>u y x hy hx⟩
end PM.Architecture.Star231MiddleKernel
