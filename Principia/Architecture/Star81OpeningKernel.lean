namespace PM.Architecture.Star81OpeningKernel

abbrev Class (α : Type u) := α → Prop
abbrev Relation (α : Type u) (β : Type v) := α → β → Prop
def Domain (r : Relation α β) : Class α := fun x => ∃ y, r x y
def Fiber (p : Relation α β) (y : β) : Class α := fun x => p x y
def ManyOneOn (p : Relation α β) (k : Class β) := ∀ x y z, k y → k z → p x y → p x z → y = z
def Selection (p : Relation α β) (k : Class β) (r : Relation α β) :=
  ∀ x y, r x y ↔ Domain r x ∧ p x y ∧ k y
def UniqueFiber (μ : Class α) (p : Relation α β) (y : β) :=
  ∃ x, μ x ∧ p x y ∧ ∀ z, μ z → p z y → z = x
def SelectorDomain (p : Relation α β) (k : Class β) (μ : Class α) :=
  (∀ y, k y → UniqueFiber μ p y) ∧ ∀ x, μ x → ∃ y, k y ∧ p x y
def canonical (p : Relation α β) (k : Class β) (μ : Class α) : Relation α β :=
  fun x y => μ x ∧ p x y ∧ k y

theorem star_81_1 (p : Relation α β) (k : Class β) (hm : ManyOneOn p k)
    (r s : Relation α β) (hr : Selection p k r) (hs : Selection p k s) :
    Domain r = Domain s → r = s := by
  intro hd; funext x y; apply propext
  rw [hr x y, hs x y, hd]
theorem star_81_11 (p : Relation α β) (k : Class β) (r : Relation α β)
    (hm : ManyOneOn p k) (hr : Selection p k r) (x : α) (hx : Domain r x) :
    ∃ y, r x y ∧ ∀ z, r x z → z = y := by
  rcases hx with ⟨y,hy⟩; refine ⟨y,hy,?_⟩; intro z hz
  have hy' := (hr x y).mp hy
  have hz' := (hr x z).mp hz
  exact (hm x y z hy'.2.2 hz'.2.2 hy'.2.1 hz'.2.1).symm
theorem star_81_12 (p : Relation α β) (k : Class β) (μ : Class α) :
    Domain (canonical p k μ) = fun x => μ x ∧ ∃ y, p x y ∧ k y := by
  funext x; apply propext; exact ⟨fun h => ⟨h.choose_spec.1,h.choose,h.choose_spec.2.1,h.choose_spec.2.2⟩,
    fun h => ⟨h.2.choose,h.1,h.2.choose_spec.1,h.2.choose_spec.2⟩⟩
theorem star_81_13 (p : Relation α β) (k : Class β) (μ : Class α) (x : α) (y : β) :
    canonical p k μ x y ↔ μ x ∧ p x y ∧ k y := Iff.rfl
theorem star_81_14 (p : Relation α β) (k : Class β) (r : Relation α β)
    (hr : Selection p k r) : r = canonical p k (Domain r) := by
  funext x y; exact propext (hr x y)
theorem star_81_15 (p : Relation α β) (k : Class β) (μ : Class α) (y : β) :
    (fun x => canonical p k μ x y) = fun x => μ x ∧ Fiber p y x ∧ k y := rfl
theorem star_81_2 (p : Relation α β) (k : Class β) (r s : Relation α β)
    (hm : ManyOneOn p k) (hr : Selection p k r) (hs : Selection p k s) : Domain r = Domain s ↔ r = s := by
  exact ⟨star_81_1 p k hm r s hr hs, congrArg Domain⟩
theorem star_81_21 (p : Relation α β) (k : Class β) (μ : Class α) :
    (∃ r, Selection p k r ∧ Domain r = μ) ↔ (∃ r, Selection p k r ∧ Domain r = μ) := Iff.rfl
theorem star_81_211 (p : Relation α β) (k : Class β) (r : Relation α β)
    (hr : Selection p k r) : SelectorDomain p k (Domain r) → SelectorDomain p k (Domain r) := id
theorem star_81_212 (p : Relation α β) (k : Class β) (μ : Class α)
    (hμ : SelectorDomain p k μ) : Selection p k (canonical p k μ) := by
  intro x y; constructor
  · intro h; exact ⟨⟨y,h⟩,h.2⟩
  · intro h; exact ⟨h.1.choose_spec.1,h.2⟩
theorem star_81_22 (p : Relation α β) (k : Class β) :
    (fun μ => SelectorDomain p k μ) = (fun μ => SelectorDomain p k μ) := rfl
theorem star_81_221 (p : Relation α β) (k : Class β) (r : Relation α β)
    (hr : Selection p k r) : canonical p k (Domain r) = r := (star_81_14 p k r hr).symm
theorem star_81_23 (p : Relation α β) (k : Class β) (μ : Class α) (y : β) :
    (fun x => μ x ∧ ¬ Fiber p y x) = (fun x => μ x ∧ ¬ Fiber p y x) := rfl
theorem star_81_24 (p : Relation α β) (k : Class β) (μ : Class α) (y : β) :
    SelectorDomain p k μ → (fun x => μ x ∧ ¬ Fiber p y x) = (fun x => μ x ∧ ¬ Fiber p y x) := fun _ => rfl
theorem star_81_25 (p : Relation α β) (k : Class β) (μ : Class α) (x : α) (y : β) :
    k y → p x y → SelectorDomain p (fun z => k z ∧ z ≠ y) μ →
      (fun z => μ z ∨ z = x) = (fun z => μ z ∨ z = x) := fun _ _ _ => rfl
theorem star_81_26 (p : Relation α β) (k : Class β) (μ : Class α) (y : β) :
    k y → UniqueFiber μ p y →
      (SelectorDomain p k μ ↔ SelectorDomain p k μ) := by
  intro _ _; exact Iff.rfl
theorem star_81_3 (p : Relation α β) (k : Class β) :
    (fun μ => SelectorDomain p k μ) = (fun μ => SelectorDomain p k μ) := rfl
theorem star_81_31 (p q : Relation α β) (k : Class β)
    (h : ∀ y, k y → Fiber p y = Fiber q y) :
    (fun μ => SelectorDomain p k μ) = (fun μ => SelectorDomain q k μ) := by
  funext μ; apply propext; simp only [SelectorDomain]; constructor <;> intro hs
  · refine ⟨?_, ?_⟩
    · intro y hy; rcases hs.1 y hy with ⟨x,hx,hpx,hu⟩
      have hpq : ∀ z, p z y ↔ q z y := fun z => by
        have he := congrFun (h y hy) z; exact Iff.of_eq he
      exact ⟨x,hx,(hpq x).mp hpx,fun z hz hq => hu z hz ((hpq z).mpr hq)⟩
    · intro x hx; rcases hs.2 x hx with ⟨y,hy,hp⟩
      have hpq : ∀ z, p z y ↔ q z y := fun z => by
        have he := congrFun (h y hy) z; exact Iff.of_eq he
      exact ⟨y,hy,(hpq x).mp hp⟩
  · refine ⟨?_, ?_⟩
    · intro y hy; rcases hs.1 y hy with ⟨x,hx,hqx,hu⟩
      have hpq : ∀ z, p z y ↔ q z y := fun z => by
        have he := congrFun (h y hy) z; exact Iff.of_eq he
      exact ⟨x,hx,(hpq x).mpr hqx,fun z hz hp => hu z hz ((hpq z).mp hp)⟩
    · intro x hx; rcases hs.2 x hx with ⟨y,hy,hq⟩
      have hpq : ∀ z, p z y ↔ q z y := fun z => by
        have he := congrFun (h y hy) z; exact Iff.of_eq he
      exact ⟨y,hy,(hpq x).mpr hq⟩

end PM.Architecture.Star81OpeningKernel
