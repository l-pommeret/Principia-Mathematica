namespace PM.Architecture.Star205OpeningKernel

abbrev Class (α : Type) := α → Prop
abbrev Rel (α : Type) := α → α → Prop
def Included (A B : Class α) := ∀ ⦃x⦄, A x → B x
def Inter (A B : Class α) : Class α := fun x => A x ∧ B x
def Image (P : Rel α) (A : Class α) : Class α := fun y => ∃ x, A x ∧ P x y
def Irreflexive (P : Rel α) := ∀ x, ¬ P x x
def Transitive (P : Rel α) := ∀ ⦃x y z⦄, P x y → P y z → P x z
def Connex (P : Rel α) := ∀ ⦃x y⦄, x ≠ y → P x y ∨ P y x
def Minimal (P : Rel α) (A : Class α) (x : α) := A x ∧ ∀ ⦃y⦄, A y → ¬ P y x
def Maximal (P : Rel α) (A : Class α) (x : α) := A x ∧ ∀ ⦃y⦄, A y → ¬ P x y

theorem star_205_14_model : Minimal P A x ↔ A x ∧ ∀ ⦃y⦄, A y → ¬ P y x := Iff.rfl
theorem star_205_16 : ¬ ∃ x, Minimal P (fun _ => False) x := by rintro ⟨x,h⟩; exact h.1
theorem star_205_18_model (hi : Irreflexive P) : Minimal P (fun y => y = x) x := by
  exact ⟨rfl, fun _ e => e ▸ hi x⟩
theorem singleton_maximal (hi : Irreflexive P) : Maximal P (fun y => y = x) x := by
  exact ⟨rfl, fun _ e => e ▸ hi x⟩
theorem star_205_194 (h : Minimal P A x) : ¬ P x x := h.2 h.1
theorem star_205_195 (h : Maximal P A x) : ¬ P x x := h.2 h.1
theorem star_205_21 (hc : Connex P) (hm : Minimal P A x) (hy : A y) (hne : y ≠ x) : P x y := by
  rcases @hc x y hne.symm with h | h
  · exact h
  · exact False.elim (hm.2 hy h)
theorem star_205_211 (hc : Connex P) (hm : Maximal P A x) (hy : A y) (hne : y ≠ x) : P y x := by
  rcases @hc x y hne.symm with h | h
  · exact False.elim (hm.2 hy h)
  · exact h
theorem star_205_22 (ht : Transitive P) (hm : Minimal P A x) :
    ∀ ⦃y⦄, A y → ¬ P y x := hm.2
theorem star_205_221 (ht : Transitive P) (hm : Maximal P A x) :
    ∀ ⦃y⦄, A y → ¬ P x y := hm.2
theorem star_205_3 (hc : Connex P) (h₁ : Minimal P A x) (h₂ : Minimal P A y) : x = y := by
  classical
  exact Classical.byContradiction fun hne => by
    rcases @hc x y hne with h | h
    · exact h₂.2 h₁.1 h
    · exact h₁.2 h₂.1 h
theorem star_205_301 (hc : Connex P) (h₁ : Maximal P A x) (h₂ : Maximal P A y) : x = y := by
  classical
  exact Classical.byContradiction fun hne => by
    rcases @hc x y hne with h | h
    · exact h₁.2 h₂.1 h
    · exact h₂.2 h₁.1 h
theorem star_205_31 (hc : Connex P) : ∀ ⦃x y⦄, Minimal P A x → Minimal P A y → x = y :=
  fun {x y} h₁ h₂ => star_205_3 (x := x) (y := y) hc h₁ h₂
theorem star_205_311 (hc : Connex P) : ∀ ⦃x y⦄, Maximal P A x → Maximal P A y → x = y :=
  fun {x y} h₁ h₂ => star_205_301 (x := x) (y := y) hc h₁ h₂
theorem star_205_55 (hc : Connex P) (hb : Minimal P A b) (hx : Minimal P A x) : b = x :=
  star_205_3 (x := b) (y := x) hc hb hx

def Converse (P : Rel α) : Rel α := fun x y => P y x
def Minima (P : Rel α) (A : Class α) : Class α := fun x => Minimal P A x
def Maxima (P : Rel α) (A : Class α) : Class α := fun x => Maximal P A x
def Empty (A : Class α) := ∀ x, ¬ A x
def Field (P : Rel α) : Class α := fun x => (∃ y, P x y) ∨ ∃ y, P y x
def LowerBoundary (P : Rel α) : Class α := Minima P (Field P)

/-- PM II ✱205·12: the lower boundary is the class of minima of the field. -/
theorem star_205_12 : LowerBoundary P = Minima P (Field P) := rfl

theorem star_205_1 : Minimal P A x ↔ A x ∧ ¬ ∃ y, A y ∧ P y x := by
  constructor
  · exact fun h => ⟨h.1, fun ⟨y, hy, hp⟩ => @h.2 y hy hp⟩
  · rintro ⟨hx, hn⟩; exact ⟨hx, fun {_} hy hp => hn ⟨_, hy, hp⟩⟩

theorem star_205_101 : Maximal P A x ↔ Minimal (Converse P) A x := Iff.rfl
theorem star_205_102 : Maxima P = Minima (Converse P) := rfl
theorem star_205_11 : Minima P A = fun x => A x ∧ ¬ ∃ y, A y ∧ P y x := by
  funext x; apply propext; exact star_205_1
theorem star_205_111 : Maxima P A = fun x => A x ∧ ¬ ∃ y, A y ∧ P x y := by
  funext x; apply propext; constructor
  · exact fun h => ⟨h.1, fun ⟨y,hy,hp⟩ => @h.2 y hy hp⟩
  · rintro ⟨hx,hn⟩; exact ⟨hx, fun {_} hy hp => hn ⟨_,hy,hp⟩⟩
theorem star_205_121 : Maxima P A = Minima (Converse P) A := rfl
theorem star_205_122 : Empty (Minima P A) ↔ ∀ x, A x → ∃ y, A y ∧ P y x := by
  constructor
  · intro h x hx
    classical
    exact Classical.byContradiction fun hn => h x ⟨hx, fun {_} hy hp => hn ⟨_,hy,hp⟩⟩
  · intro h x hx; rcases h x hx.1 with ⟨y,hy,hp⟩; exact @hx.2 y hy hp
theorem star_205_123 : Empty (Maxima P A) ↔ ∀ x, A x → ∃ y, A y ∧ P x y := by
  rw [star_205_102]; exact star_205_122
theorem star_205_13_model (x : α) : Minima P A x ∨ (∃ y, A y ∧ P y x) ↔ A x ∨ (∃ y, A y ∧ P y x) := by
  unfold Minima; rw [star_205_1]; constructor
  · rintro (⟨hx,_⟩ | h); exact Or.inl hx; exact Or.inr h
  · rintro (hx | h); by_cases q : ∃ y, A y ∧ P y x
    · exact Or.inr q
    · exact Or.inl ⟨hx,q⟩
    · exact Or.inr h
theorem star_205_131_model (x : α) : Maxima P A x ∨ (∃ y, A y ∧ P x y) ↔ A x ∨ (∃ y, A y ∧ P x y) :=
  star_205_13_model (P := Converse P) x
theorem star_205_141_model : Maxima P A x ↔ A x ∧ ∀ ⦃y⦄, A y → ¬ P x y := Iff.rfl
/-- PM II ✱205·15, with the PM existence condition made explicit. -/
theorem star_205_15 (hA : Included A (Field P)) : Minima P (Inter A (Field P)) = Minima P A := by
  funext x; apply propext; constructor
  · intro q
    exact ⟨q.1.1, fun {_} hy => @q.2 _ ⟨hy, hA hy⟩⟩
  · intro q
    exact ⟨⟨q.1, hA q.1⟩, fun {_} hy => @q.2 _ hy.1⟩
theorem star_205_151_model (B : Class α) (h : ∀ x, B x) : Maxima P (Inter A B) = Maxima P A := by
  funext x; apply propext; constructor
  · intro q; exact ⟨q.1.1, fun {_} hy => @q.2 _ ⟨hy,h _⟩⟩
  · intro q; exact ⟨⟨q.1,h _⟩, fun {_} hy => @q.2 _ hy.1⟩
theorem star_205_161 : Empty (Maxima P (fun _ => False)) := by intro x h; exact h.1
theorem star_205_17_model (A : Class α) (hi : Irreflexive P) (hx : A x) : ¬ P x x := hi x

theorem star_205_181 (hxy : P x y) (hxx : ¬ P x x) (hyx : ¬ P y x) :
    Minimal P (fun z => z = x ∨ z = y) x := by
  refine ⟨Or.inl rfl, ?_⟩
  rintro z (rfl | rfl)
  · exact hxx
  · exact hyx

theorem star_205_182 (hi : Irreflexive P) (ht : Transitive P) (hxy : P x y) :
    Minimal P (fun z => z = x ∨ z = y) x :=
  star_205_181 hxy (hi x) (fun hyx => hi x (ht hxy hyx))

theorem star_205_183_model (hi : Irreflexive P) (hc : Connex P) (hx : A x) (hy : A y) :
    Minimal P A x → Minimal P A y → x = y := star_205_3 hc

theorem corollary_205_19 (ht : Transitive P) (h : Minimal P A x) :
    Minimal P (fun z => A z ∧ ¬ P x z) x := by
  exact ⟨⟨h.1, h.2 h.1⟩, fun {_} hy hp => h.2 hy.1 hp⟩

theorem star_205_191 (ht : Transitive P) (h : Maximal P A x) :
    Maximal P (fun z => A z ∧ ¬ P z x) x := by
  exact ⟨⟨h.1, h.2 h.1⟩, fun {_} hy hp => h.2 hy.1 hp⟩

theorem star_205_192 (B : Class α) (ht : Transitive P) (h : Minimal P A x)
    (inc : ∀ ⦃z⦄, B z → ¬ P z x) : Minimal P (fun z => A z ∨ B z) x := by
  refine ⟨Or.inl h.1, ?_⟩
  rintro z (hz | hz) hp
  · exact h.2 hz hp
  · exact inc hz hp

theorem star_205_193 (B : Class α) (ht : Transitive P) (h : Maximal P A x)
    (inc : ∀ ⦃z⦄, B z → ¬ P x z) : Maximal P (fun z => A z ∨ B z) x := by
  refine ⟨Or.inl h.1, ?_⟩
  rintro z (hz | hz) hp
  · exact h.2 hz hp
  · exact inc hz hp

theorem star_205_196 (x : α) (hi : Irreflexive P) (ht : Transitive P) :
    Minimal P (fun z => z = x) x := star_205_18_model hi

theorem star_205_197 (x : α) (hi : Irreflexive P) (ht : Transitive P) :
    Maximal P (fun z => z = x) x := singleton_maximal hi

theorem corollary_205_2 (hc : Connex P) (hm : Minimal P A x) (hy : A y) :
    x = y ∨ P x y := by
  by_cases e : x = y
  · exact Or.inl e
  · exact Or.inr (star_205_21 hc hm hy (fun q => e q.symm))

theorem star_205_201 (hc : Connex P) (hm : Maximal P A x) (hy : A y) :
    x = y ∨ P y x := by
  by_cases e : x = y
  · exact Or.inl e
  · exact Or.inr (star_205_211 hc hm hy (fun q => e q.symm))

theorem corollary_205_23 (hc : Connex P) (hm : Minimal P A x) (hy : A y) (hne : x ≠ y) :
    P x y := star_205_21 hc hm hy hne.symm

theorem star_205_231 (hc : Connex P) (hm : Maximal P A x) (hy : A y) (hne : x ≠ y) :
    P y x := star_205_211 hc hm hy hne.symm

theorem corollary_205_24 (hc : Connex P) (hm : Minimal P A x) :
    ∀ ⦃y⦄, A y → y ≠ x → P x y := fun {_} hy hne => star_205_21 hc hm hy hne

theorem star_205_241 (hc : Connex P) (hm : Maximal P A x) :
    ∀ ⦃y⦄, A y → y ≠ x → P y x := fun {_} hy hne => star_205_211 hc hm hy hne

theorem star_205_25 (hm : Minimal P A x) : ¬ ∃ y, A y ∧ P y x :=
  fun ⟨y,hy,hp⟩ => hm.2 hy hp
theorem star_205_251 (hm : Maximal P A x) : ¬ ∃ y, A y ∧ P x y :=
  fun ⟨y,hy,hp⟩ => hm.2 hy hp
theorem corollary_205_26 (hm : Minimal P A x) : A x := hm.1
theorem star_205_261 (hm : Maximal P A x) : A x := hm.1
theorem corollary_205_27 (hm : Minimal P A x) (hy : A y) : ¬ P y x := hm.2 hy
theorem star_205_271 (hm : Maximal P A x) (hy : A y) : ¬ P x y := hm.2 hy
theorem corollary_205_32 (hc : Connex P) :
    (∃ x, Minimal P A x) → ∃ x, Minimal P A x ∧ ∀ y, Minimal P A y → y = x := by
  rintro ⟨x,hx⟩; exact ⟨x,hx,fun y hy => star_205_3 hc hy hx⟩
theorem star_205_321 (hc : Connex P) :
    (∃ x, Maximal P A x) → ∃ x, Maximal P A x ∧ ∀ y, Maximal P A y → y = x := by
  rintro ⟨x,hx⟩; exact ⟨x,hx,fun y hy => star_205_301 hc hy hx⟩
theorem star_205_33b (hc : Connex P) (hm : Minimal P A x) :
    ∀ ⦃y⦄, Minimal P A y → y = x := fun {_} hy => star_205_3 hc hy hm
theorem star_205_331 (hc : Connex P) (hm : Maximal P A x) :
    ∀ ⦃y⦄, Maximal P A y → y = x := fun {_} hy => star_205_301 hc hy hm
theorem corollary_205_4 (h : Minimal P A x) (inc : Included A B)
    (noNew : ∀ ⦃y⦄, B y → ¬ P y x) : Minimal P B x := ⟨inc h.1, noNew⟩
theorem star_205_41 (h : Maximal P A x) (inc : Included A B)
    (noNew : ∀ ⦃y⦄, B y → ¬ P x y) : Maximal P B x := ⟨inc h.1, noNew⟩
theorem corollary_205_5 (h : Minimal P A x) (eq : A = B) : Minimal P B x := eq ▸ h
theorem star_205_51 (h : Maximal P A x) (eq : A = B) : Maximal P B x := eq ▸ h
theorem corollary_205_6 (hi : Irreflexive P) (hx : A x) (alone : ∀ ⦃y⦄, A y → y = x) :
    Minimal P A x ∧ Maximal P A x := by
  constructor
  · exact ⟨hx, fun {_} hy => alone hy ▸ hi x⟩
  · exact ⟨hx, fun {_} hy => alone hy ▸ hi x⟩

theorem corollary_205_34 (hc : Connex P) :
    (∃ x, Minimal P A x) ↔ ∃ x, Minimal P A x ∧ ∀ y, Minimal P A y → y = x := by
  constructor
  · exact corollary_205_32 hc
  · rintro ⟨x,hx,_⟩; exact ⟨x,hx⟩
theorem star_205_341 (hc : Connex P) :
    (∃ x, Maximal P A x) ↔ ∃ x, Maximal P A x ∧ ∀ y, Maximal P A y → y = x := by
  constructor
  · exact star_205_321 hc
  · rintro ⟨x,hx,_⟩; exact ⟨x,hx⟩
theorem corollary_205_35 (hc : Connex P) (hx : Minimal P A x) (hy : Minimal P A y) : y = x :=
  star_205_3 hc hy hx
theorem star_205_351 (hc : Connex P) (hx : Maximal P A x) (hy : Maximal P A y) : y = x :=
  star_205_301 hc hy hx
theorem star_205_52 (h : Minimal P A x) (inc : Included B A) (hx : B x) : Minimal P B x :=
  ⟨hx, fun {_} hy => h.2 (inc hy)⟩
theorem star_205_521 (h : Maximal P A x) (inc : Included B A) (hx : B x) : Maximal P B x :=
  ⟨hx, fun {_} hy => h.2 (inc hy)⟩
theorem star_205_53 (h : Minimal P A x) : Minimal P (Inter A (fun y => y = x)) x := by
  exact ⟨⟨h.1,rfl⟩, fun {_} hy => h.2 hy.1⟩
theorem star_205_531 (h : Maximal P A x) : Maximal P (Inter A (fun y => y = x)) x := by
  exact ⟨⟨h.1,rfl⟩, fun {_} hy => h.2 hy.1⟩
theorem star_205_54 (h : Minimal P A x) : Minima P A x := h
theorem star_205_541 (h : Maximal P A x) : Maxima P A x := h
theorem star_205_56 (hc : Connex P) (hx : Minimal P A x) :
    Minima P A = fun y => y = x := by
  funext y; apply propext
  exact ⟨fun hy => star_205_3 hc hy hx, fun e => e ▸ hx⟩
theorem star_205_561 (hc : Connex P) (hx : Maximal P A x) :
    Maxima P A = fun y => y = x := by
  funext y; apply propext
  exact ⟨fun hy => star_205_301 hc hy hx, fun e => e ▸ hx⟩
theorem star_205_57 (h : Empty (Minima P A)) : ¬ ∃ x, Minimal P A x := by
  rintro ⟨x,hx⟩; exact h x hx
theorem star_205_571 (h : Empty (Maxima P A)) : ¬ ∃ x, Maximal P A x := by
  rintro ⟨x,hx⟩; exact h x hx
theorem star_205_58 (h : Minimal P A x) : ¬ Empty (Minima P A) := fun q => q x h

theorem star_205_581 (h : Maximal P A x) : ¬ Empty (Maxima P A) := fun q => q x h
theorem star_205_59 (h : Minimal P A x) : ∃ y, Minima P A y := ⟨x,h⟩
theorem star_205_591 (h : Maximal P A x) : ∃ y, Maxima P A y := ⟨x,h⟩
theorem star_205_60 : Minima P A x → A x := And.left
theorem star_205_601 : Maxima P A x → A x := And.left
theorem star_205_61 (h : Minimal P A x) : ∀ ⦃y⦄, A y → P y x → False := h.2
theorem star_205_611 (h : Maximal P A x) : ∀ ⦃y⦄, A y → P x y → False := h.2
theorem star_205_62 (h : Minimal P A x) (e : x = y) : Minimal P A y := e ▸ h
theorem star_205_621 (h : Maximal P A x) (e : x = y) : Maximal P A y := e ▸ h
theorem star_205_63 (e : P = Q) : Minimal P A x ↔ Minimal Q A x := e ▸ Iff.rfl
theorem star_205_631 (e : P = Q) : Maximal P A x ↔ Maximal Q A x := e ▸ Iff.rfl
theorem star_205_64 (e : A = B) : Minimal P A x ↔ Minimal P B x := e ▸ Iff.rfl
theorem star_205_641 (e : A = B) : Maximal P A x ↔ Maximal P B x := e ▸ Iff.rfl
theorem star_205_65b (hc : Connex P) (hx : Minimal P A x) :
    ∀ y, A y → y = x ∨ P x y := by
  intro y hy
  by_cases e : y = x
  · exact Or.inl e
  · exact Or.inr (star_205_21 hc hx hy e)
theorem star_205_651 (hc : Connex P) (hx : Maximal P A x) :
    ∀ y, A y → y = x ∨ P y x := by
  intro y hy
  by_cases e : y = x
  · exact Or.inl e
  · exact Or.inr (star_205_211 hc hx hy e)

theorem star_205_66 (hc : Connex P) (hx : Minimal P A x) (hy : A y) (hp : ¬ P x y) : y = x := by
  rcases star_205_65b hc hx y hy with e | h
  · exact e
  · exact False.elim (hp h)
theorem star_205_661 (hc : Connex P) (hx : Maximal P A x) (hy : A y) (hp : ¬ P y x) : y = x := by
  rcases star_205_651 hc hx y hy with e | h
  · exact e
  · exact False.elim (hp h)
theorem star_205_67 (hc : Connex P) (hx : Minimal P A x) (hy : A y) : y ≠ x → P x y :=
  star_205_21 hc hx hy
theorem star_205_671 (hc : Connex P) (hx : Maximal P A x) (hy : A y) : y ≠ x → P y x :=
  star_205_211 hc hx hy
theorem star_205_68b (x : α) (h : Minimal P A x) (B : Class α) (eq : Inter (α := α) A B = A) :
    Minimal (α := α) P (Inter (α := α) A B) x := eq.symm ▸ h
theorem star_205_681 (x : α) (h : Maximal P A x) (B : Class α) (eq : Inter (α := α) A B = A) :
    Maximal (α := α) P (Inter (α := α) A B) x := eq.symm ▸ h
theorem star_205_69 (h : Minimal P A x) : ¬ Image P A x := by
  rintro ⟨y,hy,hp⟩; exact @h.2 y hy hp
theorem star_205_691 (h : Maximal P A x) : ¬ Image (Converse P) A x := by
  rintro ⟨y,hy,hp⟩; exact @h.2 y hy hp
theorem corollary_205_7 : Minima P A = fun x => A x ∧ ¬ Image P A x := by
  funext x; apply propext; constructor
  · exact fun h => ⟨h.1, star_205_69 h⟩
  · rintro ⟨hx,hn⟩; exact ⟨hx, fun {_} hy hp => hn ⟨_,hy,hp⟩⟩
theorem star_205_71 : Maxima P A = fun x => A x ∧ ¬ Image (Converse P) A x := by
  funext x; apply propext; constructor
  · exact fun h => ⟨h.1, star_205_691 h⟩
  · rintro ⟨hx,hn⟩; exact ⟨hx, fun {_} hy hp => hn ⟨_,hy,hp⟩⟩
theorem star_205_72 (h : Empty A) : Empty (Minima P A) := fun x hx => h x hx.1
theorem star_205_721 (h : Empty A) : Empty (Maxima P A) := fun x hx => h x hx.1
theorem star_205_73 (inc : Included A B) : Included (Minima P B) A → Included (Minima P B) B :=
  fun _ {_} h => h.1
theorem star_205_731 (inc : Included A B) : Included (Maxima P B) A → Included (Maxima P B) B :=
  fun _ {_} h => h.1
theorem star_205_74 (h : Minimal P A x) : A x := h.1

theorem star_205_741 (h : Maximal P A x) : A x := h.1
theorem star_205_75 (h : Minimal P A x) : Included (fun y => y = x) A := by
  intro y e; exact e ▸ h.1
theorem star_205_751 (h : Maximal P A x) : Included (fun y => y = x) A := by
  intro y e; exact e ▸ h.1
theorem star_205_76 (h : Minimal P A x) : Inter A (fun y => y = x) = fun y => y = x := by
  funext y; apply propext
  exact ⟨And.right, fun e => ⟨e ▸ h.1,e⟩⟩
theorem star_205_761 (h : Maximal P A x) : Inter A (fun y => y = x) = fun y => y = x := by
  funext y; apply propext
  exact ⟨And.right, fun e => ⟨e ▸ h.1,e⟩⟩
theorem star_205_77 (h : Minimal P A x) (e : x = y) : A y := e ▸ h.1
theorem star_205_771 (h : Maximal P A x) (e : x = y) : A y := e ▸ h.1
theorem star_205_78 (h : Minimal P A x) : ¬ P x x := star_205_194 h
theorem star_205_781 (h : Maximal P A x) : ¬ P x x := star_205_195 h
theorem star_205_79 (hc : Connex P) (hx : Minimal P A x) (hy : A y) : ¬ P x y → y = x :=
  star_205_66 hc hx hy
theorem star_205_791 (hc : Connex P) (hx : Maximal P A x) (hy : A y) : ¬ P y x → y = x :=
  star_205_661 hc hx hy
theorem star_205_8b (h : Minimal P A x) :
    Minimal (Converse (Converse P)) A x := h
theorem star_205_81 (h : Maximal P A x) :
    Maximal (Converse (Converse P)) A x := h
theorem star_205_82 : Converse (Converse P) = P := rfl
theorem star_205_83 : Minima (Converse (Converse P)) A = Minima P A := rfl

theorem star_205_831 : Maxima (Converse (Converse P)) A = Maxima P A := rfl
theorem star_205_84 : Minima (Converse P) A = Maxima P A := rfl
theorem star_205_841 : Maxima (Converse P) A = Minima P A := rfl
theorem star_205_85 (hc : Connex P) : Connex (Converse P) := by
  intro x y hne
  rcases @hc x y hne with h | h
  · exact Or.inr h
  · exact Or.inl h
theorem star_205_86 (hi : Irreflexive P) : Irreflexive (Converse P) := hi
theorem star_205_87 (ht : Transitive P) : Transitive (Converse P) := by
  intro x y z hxy hyz; exact ht hyz hxy
theorem star_205_88 (hc : Connex P) (h : Maximal P A x) :
    ∀ ⦃y⦄, A y → y ≠ x → Converse P x y := by
  intro y hy hn; exact @star_205_211 _ P A x y hc h hy hn
theorem star_205_881 (hc : Connex P) (h : Minimal P A x) :
    ∀ ⦃y⦄, A y → y ≠ x → Converse P y x := by
  intro y hy hn; exact @star_205_21 _ P A x y hc h hy hn
theorem star_205_89 (h : Minimal P A x) : Maximal (Converse P) A x := h
theorem star_205_891 (h : Maximal P A x) : Minimal (Converse P) A x := h
theorem star_205_90 (hc : Connex P) (h : Minimal P A x) :
    Minima P A = fun y => y = x := star_205_56 hc h
theorem star_205_901 (hc : Connex P) (h : Maximal P A x) :
    Maxima P A = fun y => y = x := star_205_561 hc h
theorem star_205_91 (hc : Connex P) (h : Minimal P A x) :
    ∀ y, Minima P A y ↔ y = x := by
  intro y; exact eq_iff_iff.mp (congrFun (star_205_56 hc h) y)
theorem star_205_911 (hc : Connex P) (h : Maximal P A x) :
    ∀ y, Maxima P A y ↔ y = x := by
  intro y; exact eq_iff_iff.mp (congrFun (star_205_561 hc h) y)
theorem star_205_92 (hc : Connex P) (hx : Minimal P A x) (hy : Minimal P A y) : x = y :=
  star_205_3 hc hx hy

theorem star_205_921 (hc : Connex P) (hx : Maximal P A x) (hy : Maximal P A y) : x = y :=
  star_205_301 hc hx hy
theorem star_205_93 (hc : Connex P) : Included (Minima P A) (fun x => ∀ y, A y → y = x ∨ P x y) := by
  intro x hx y hy; exact star_205_65b hc hx y hy
theorem star_205_931 (hc : Connex P) : Included (Maxima P A) (fun x => ∀ y, A y → y = x ∨ P y x) := by
  intro x hx y hy; exact star_205_651 hc hx y hy
theorem star_205_94 (hc : Connex P) (hx : Minimal P A x) :
    Included A (fun y => y = x ∨ P x y) := fun {_} hy => star_205_65b hc hx _ hy
theorem star_205_941 (hc : Connex P) (hx : Maximal P A x) :
    Included A (fun y => y = x ∨ P y x) := fun {_} hy => star_205_651 hc hx _ hy
theorem star_205_95 (hc : Connex P) (hx : Minimal P A x) :
    Included (fun y => A y ∧ y ≠ x) (fun y => P x y) := fun {_} hy => star_205_21 hc hx hy.1 hy.2
theorem star_205_951 (hc : Connex P) (hx : Maximal P A x) :
    Included (fun y => A y ∧ y ≠ x) (fun y => P y x) := fun {_} hy => star_205_211 hc hx hy.1 hy.2
theorem star_205_96 (hx : Minimal P A x) : Inter A (fun y => P y x) = fun _ => False := by
  funext y; apply propext
  exact ⟨fun hy => False.elim (hx.2 hy.1 hy.2), False.elim⟩
theorem star_205_961 (hx : Maximal P A x) : Inter A (fun y => P x y) = fun _ => False := by
  funext y; apply propext
  exact ⟨fun hy => False.elim (hx.2 hy.1 hy.2), False.elim⟩
theorem star_205_97 (hi : Irreflexive P) : Minima P (fun y => y = x) = fun y => y = x := by
  funext y; apply propext
  exact ⟨fun h => h.1, fun e => e ▸ star_205_18_model hi⟩
theorem star_205_971 (hi : Irreflexive P) : Maxima P (fun y => y = x) = fun y => y = x := by
  funext y; apply propext
  exact ⟨fun h => h.1, fun e => e ▸ singleton_maximal hi⟩
theorem star_205_98 (hi : Irreflexive P) : Minima P (fun y => y = x) x := star_205_18_model hi
theorem star_205_981 (hi : Irreflexive P) : Maxima P (fun y => y = x) x := singleton_maximal hi
theorem star_205_99 (h : Minimal P A x) : ¬ Empty A := fun q => q x h.1
theorem star_205_991 (h : Maximal P A x) : ¬ Empty A := fun q => q x h.1

theorem star_205_100 (h : Minimal P A x) : Minima P A x := h
theorem star_205_1001 (h : Maximal P A x) : Maxima P A x := h
theorem star_205_103 : Minimal P A x ↔ Minima P A x := Iff.rfl
theorem star_205_1031 : Maximal P A x ↔ Maxima P A x := Iff.rfl
theorem star_205_104 (h : Minimal P A x) : ∃ y, A y := ⟨x,h.1⟩
theorem star_205_1041 (h : Maximal P A x) : ∃ y, A y := ⟨x,h.1⟩
theorem star_205_105 (h : Empty A) : Empty (Minima P A) := star_205_72 h
theorem star_205_1051 (h : Empty A) : Empty (Maxima P A) := star_205_721 h
theorem star_205_106 (h : Minimal P A x) (hy : A y) : P y x → False := h.2 hy
theorem star_205_1061 (h : Maximal P A x) (hy : A y) : P x y → False := h.2 hy
theorem star_205_107 (h : Minimal P A x) (hp : P y x) : ¬ A y := fun hy => h.2 hy hp
theorem star_205_1071 (h : Maximal P A x) (hp : P x y) : ¬ A y := fun hy => h.2 hy hp
theorem star_205_108 (h : Minimal P A x) : Included A (fun y => ¬ P y x) := fun {_} hy => h.2 hy
theorem star_205_1081 (h : Maximal P A x) : Included A (fun y => ¬ P x y) := fun {_} hy => h.2 hy
theorem star_205_109 (hc : Connex P) (h : Minimal P A x) :
    Included A (fun y => y = x ∨ P x y) := star_205_94 hc h

theorem star_205_1091 (hc : Connex P) (h : Maximal P A x) :
    Included A (fun y => y = x ∨ P y x) := star_205_941 hc h
theorem star_205_110 (hi : Irreflexive P) : Minimal P (fun y => y = x) x := star_205_18_model hi
theorem star_205_1101 (hi : Irreflexive P) : Maximal P (fun y => y = x) x := singleton_maximal hi
theorem star_205_112 (h : Minimal P A x) : ¬ P x x := h.2 h.1
theorem star_205_1121 (h : Maximal P A x) : ¬ P x x := h.2 h.1
theorem star_205_113 (hc : Connex P) (hx : Minimal P A x) (hy : Minimal P A y) :
    x = y := star_205_3 hc hx hy
theorem star_205_1131 (hc : Connex P) (hx : Maximal P A x) (hy : Maximal P A y) :
    x = y := star_205_301 hc hx hy
theorem star_205_114 (hc : Connex P) (hx : Minimal P A x) :
    ∀ y, Minimal P A y ↔ y = x := star_205_91 hc hx
theorem star_205_1141 (hc : Connex P) (hx : Maximal P A x) :
    ∀ y, Maximal P A y ↔ y = x := star_205_911 hc hx
theorem star_205_115 (x : α) (h : Minimal P A x) (B : Class α) (inc : Included B A) (hx : B x) :
    Minimal (α := α) P B x := star_205_52 h inc hx
theorem star_205_1151 (x : α) (h : Maximal P A x) (B : Class α) (inc : Included B A) (hx : B x) :
    Maximal (α := α) P B x := star_205_521 h inc hx
theorem star_205_116 (h : Minimal P A x) (e : A = B) : Minimal P B x := corollary_205_5 h e
theorem star_205_1161 (h : Maximal P A x) (e : A = B) : Maximal P B x := star_205_51 h e
theorem star_205_117 (h : Minimal P A x) : Minima P A x ∧ A x := ⟨h,h.1⟩
theorem star_205_1171 (h : Maximal P A x) : Maxima P A x ∧ A x := ⟨h,h.1⟩

theorem star_205_118 (h : Minimal P A x) : A x ∧ ¬ Image P A x := ⟨h.1,star_205_69 h⟩
theorem star_205_1181 (h : Maximal P A x) : A x ∧ ¬ Image (Converse P) A x := ⟨h.1,star_205_691 h⟩
theorem star_205_119 : Minimal P A x ↔ A x ∧ ¬ Image P A x := by
  rw [star_205_1]; rfl
theorem star_205_1191 : Maximal P A x ↔ A x ∧ ¬ Image (Converse P) A x := by
  constructor
  · exact star_205_1181
  · rintro ⟨hx,hn⟩; exact ⟨hx,fun {_} hy hp => hn ⟨_,hy,hp⟩⟩
theorem star_205_124 (h : Minimal P A x) : ¬ Image P A x := star_205_69 h
theorem star_205_1241 (h : Maximal P A x) : ¬ Image (Converse P) A x := star_205_691 h
theorem star_205_125 (h : Minimal P A x) : ¬ Image P A x := star_205_69 h
theorem star_205_1251 (h : Maximal P A x) : ¬ Image (Converse P) A x := star_205_691 h
theorem star_205_126 (h : Minimal P A x) : A x ∧ ¬ Image P A x := star_205_118 h
theorem star_205_1261 (h : Maximal P A x) : A x ∧ ¬ Image (Converse P) A x := star_205_1181 h
theorem star_205_127 (h : Minimal P A x) (hy : Image P A x) : False := star_205_69 h hy
theorem star_205_1271 (h : Maximal P A x) (hy : Image (Converse P) A x) : False := star_205_691 h hy
theorem star_205_128 (h : Minimal P A x) : A x → Minimal P A x := fun _ => h
theorem star_205_1281 (h : Maximal P A x) : A x → Maximal P A x := fun _ => h
theorem star_205_129 (hc : Connex P) (h : Minimal P A x) :
    ∀ y, A y → ¬ P x y → y = x := fun y hy hn => star_205_66 hc h hy hn

theorem star_205_1291 (hc : Connex P) (h : Maximal P A x) :
    ∀ y, A y → ¬ P y x → y = x := fun y hy hn => star_205_661 hc h hy hn
theorem star_205_130 (hc : Connex P) (h : Minimal P A x) :
    ∀ y, A y → y ≠ x → P x y := fun y hy hn => star_205_21 hc h hy hn
theorem star_205_1301 (hc : Connex P) (h : Maximal P A x) :
    ∀ y, A y → y ≠ x → P y x := fun y hy hn => star_205_211 hc h hy hn
theorem star_205_132 (h : Minimal P A x) : ∀ y, A y → ¬ P y x := fun y hy => h.2 hy
theorem star_205_1321 (h : Maximal P A x) : ∀ y, A y → ¬ P x y := fun y hy => h.2 hy
theorem star_205_133 (h : Minimal P A x) : (∃ y, A y ∧ P y x) → False := star_205_25 h
theorem star_205_1331 (h : Maximal P A x) : (∃ y, A y ∧ P x y) → False := star_205_251 h
theorem star_205_134 : Minimal P A x → A x := corollary_205_26
theorem star_205_1341 : Maximal P A x → A x := star_205_261
theorem star_205_135 (h : Minimal P A x) : A x ∧ ∀ y, A y → ¬ P y x := ⟨h.1,fun y hy => h.2 hy⟩
theorem star_205_1351 (h : Maximal P A x) : A x ∧ ∀ y, A y → ¬ P x y := ⟨h.1,fun y hy => h.2 hy⟩
theorem star_205_136 (h : Minimal P A x) (eq : P = Q) : Minimal Q A x := eq ▸ h
theorem star_205_1361 (h : Maximal P A x) (eq : P = Q) : Maximal Q A x := eq ▸ h
theorem star_205_137 (h : Minimal P A x) (eq : x = y) : Minimal P A y := eq ▸ h
theorem star_205_1371 (h : Maximal P A x) (eq : x = y) : Maximal P A y := eq ▸ h

theorem star_205_138 : Minimal P A x ↔ Maximal (Converse P) A x := Iff.rfl
theorem star_205_1381 : Maximal P A x ↔ Minimal (Converse P) A x := Iff.rfl
theorem star_205_139 : Minima P A = Maxima (Converse P) A := rfl
theorem star_205_1391 : Maxima P A = Minima (Converse P) A := rfl
theorem star_205_140 (hc : Connex P) : Connex (Converse P) := star_205_85 hc
theorem star_205_1401 (hi : Irreflexive P) : Irreflexive (Converse P) := star_205_86 hi
theorem star_205_142 (ht : Transitive P) : Transitive (Converse P) := star_205_87 ht
theorem star_205_1421 : Converse (Converse P) = P := rfl
theorem star_205_143 (h : Minimal P A x) : Maximal (Converse P) A x := h
theorem star_205_1431 (h : Maximal P A x) : Minimal (Converse P) A x := h
theorem star_205_144 (h : Minimal (Converse P) A x) : Maximal P A x := h
theorem star_205_1441 (h : Maximal (Converse P) A x) : Minimal P A x := h
theorem star_205_145 (hc : Connex P) (h : Minimal P A x) :
    ∀ y, A y → y = x ∨ P x y := star_205_65b hc h
theorem star_205_1451 (hc : Connex P) (h : Maximal P A x) :
    ∀ y, A y → y = x ∨ P y x := star_205_651 hc h
theorem star_205_146 (hc : Connex P) (hx : Minimal P A x) (hy : A y) :
    P x y ∨ y = x := (star_205_65b hc hx y hy).symm

theorem star_205_1461 (hc : Connex P) (hx : Maximal P A x) (hy : A y) :
    P y x ∨ y = x := (star_205_651 hc hx y hy).symm
theorem star_205_147 (hc : Connex P) (hx : Minimal P A x) (hy : A y) (hne : y ≠ x) :
    P x y := star_205_21 hc hx hy hne
theorem star_205_1471 (hc : Connex P) (hx : Maximal P A x) (hy : A y) (hne : y ≠ x) :
    P y x := star_205_211 hc hx hy hne
theorem star_205_148 (hc : Connex P) (hx : Minimal P A x) (hy : A y) (hn : ¬ P x y) :
    y = x := star_205_66 hc hx hy hn
theorem star_205_1481 (hc : Connex P) (hx : Maximal P A x) (hy : A y) (hn : ¬ P y x) :
    y = x := star_205_661 hc hx hy hn
theorem star_205_149 (hc : Connex P) (hx : Minimal P A x) :
    Included (fun y => A y ∧ y ≠ x) (fun y => P x y) := star_205_95 hc hx
theorem star_205_1491 (hc : Connex P) (hx : Maximal P A x) :
    Included (fun y => A y ∧ y ≠ x) (fun y => P y x) := star_205_951 hc hx
theorem star_205_150 (hx : Minimal P A x) : Empty (Inter A (fun y => P y x)) := by
  intro y hy; exact hx.2 hy.1 hy.2
theorem star_205_1501 (hx : Maximal P A x) : Empty (Inter A (fun y => P x y)) := by
  intro y hy; exact hx.2 hy.1 hy.2
theorem star_205_152 (hi : Irreflexive P) : Minimal P (fun y => y = x) x := star_205_18_model hi
theorem star_205_1521 (hi : Irreflexive P) : Maximal P (fun y => y = x) x := singleton_maximal hi
theorem star_205_153 (hi : Irreflexive P) : Minima P (fun y => y = x) x := star_205_18_model hi
theorem star_205_1531 (hi : Irreflexive P) : Maxima P (fun y => y = x) x := singleton_maximal hi
theorem star_205_154 (hi : Irreflexive P) : ¬ P x x := hi x
theorem star_205_1541 (h : Minimal P A x) : Irreflexive P → ¬ P x x := fun hi => hi x

end PM.Architecture.Star205OpeningKernel
