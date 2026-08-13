/-! Simple-type kernel for PM I ✱84·01–·24. -/
namespace PM.Architecture.Star84Kernel
universe u
abbrev Set (α : Type u) := α → Prop
abbrev Family (α : Type u) := Set (Set α)
def empty : Set α := fun _ => False
def inter (a b : Set α) : Set α := fun x => a x ∧ b x
def Included (a b : Set α) := ∀ ⦃x⦄, a x → b x
def Exists (a : Set α) := ∃ x, a x
def singleton (a : Set α) : Family α := fun b => b = a
def units : Family α := fun a => ∃ x, a = fun y => y = x
def unitImage (a : Set α) : Family α := fun s => ∃ x, a x ∧ s = fun y => y = x
def MutuallyExclusive (κ : Family α) :=
  ∀ ⦃a b⦄, κ a → κ b → a ≠ b → ¬ Exists (inter a b)
def ClassExcl (γ κ : Family α) := MutuallyExclusive κ ∧ Included κ γ
def NonemptyExclusive (κ : Family α) := MutuallyExclusive κ ∧ ¬ κ empty
def ManyOneMembership (κ : Family α) :=
  ∀ ⦃x a b⦄, κ a → κ b → a x → b x → a = b
abbrev Rel (α : Type u) := α → Set α → Prop
def Domain (R : Rel α) : Set α := fun x => ∃ a, R x a
def Unique (p : Set α) := ∃ x, p x ∧ ∀ y, p y → y = x
def Selects (κ : Family α) (R : Rel α) :=
  (∀ ⦃x a⦄, R x a → κ a ∧ a x) ∧ (∀ ⦃a⦄, κ a → Unique (fun x => R x a))
def ManyOneRel (R : Rel α) := ∀ ⦃x a b⦄, R x a → R x b → a = b
def sum (κ : Family α) : Set α := fun x => ∃ a, κ a ∧ a x
def familyDiff (κ : Family α) (a : Set α) : Family α := fun b => κ b ∧ b ≠ a
def setDiff (a b : Set α) : Set α := fun x => a x ∧ ¬ b x
def HitsOnce (κ : Family α) (mu : Set α) := ∀ ⦃a⦄, κ a → Unique (inter mu a)
def SelectedDomains (κ : Family α) : Family α := fun mu => ∃ R, Selects κ R ∧ mu = Domain R
def image (R : α → α → Prop) (a : Set α) : Set α := fun y => ∃ x, a x ∧ R x y
def imageFamily (R : α → α → Prop) (κ : Family α) : Family α := fun b => ∃ a, κ a ∧ b = image R a
def ImageInjective (R : α → α → Prop) := ∀ ⦃x z y⦄, R x y → R z y → x = z
def familyUnion (κ lam : Family α) : Family α := fun a => κ a ∨ lam a
def CrossDisjoint (κ lam : Family α) := ∀ ⦃a b⦄, κ a → lam b → a ≠ b → ¬ Exists (inter a b)
def CrossSelectable (κ lam : Family α) := Included κ (SelectedDomains lam)

theorem star_84_01 (κ : Family α) : MutuallyExclusive κ ↔
    ∀ ⦃a b⦄, κ a → κ b → a ≠ b → ¬ Exists (inter a b) := Iff.rfl
theorem star_84_02 (γ κ : Family α) : ClassExcl γ κ ↔
    MutuallyExclusive κ ∧ Included κ γ := Iff.rfl
theorem star_84_03 (κ : Family α) : NonemptyExclusive κ ↔
    MutuallyExclusive κ ∧ ¬ κ empty := Iff.rfl
theorem star_84_1 (κ : Family α) : MutuallyExclusive κ ↔
    ∀ ⦃a b⦄, κ a → κ b → a ≠ b → ¬ Exists (inter a b) := Iff.rfl
theorem star_84_11 (κ : Family α) : MutuallyExclusive κ ↔
    ∀ ⦃a b⦄, κ a → κ b → Exists (inter a b) → a = b := by
  constructor
  · intro h a b ha hb hi
    classical
    by_cases hn : a = b
    · exact hn
    · exact False.elim (h ha hb hn hi)
  · intro h a b ha hb hn hi; exact hn (h (a := a) (b := b) ha hb hi)
theorem star_84_12 (γ κ : Family α) : ClassExcl γ κ ↔
    MutuallyExclusive κ ∧ Included κ γ := Iff.rfl
theorem star_84_121 (γ κ : Family α) : ClassExcl γ κ ↔
    (∀ ⦃a b⦄, κ a → κ b → Exists (inter a b) → a = b) ∧ Included κ γ := by
  rw [star_84_12, star_84_11]
theorem star_84_13 (κ : Family α) : NonemptyExclusive κ ↔
    MutuallyExclusive κ ∧ ¬ κ empty := Iff.rfl
theorem star_84_131 (κ : Family α) : NonemptyExclusive κ ↔
    (∀ ⦃a b⦄, κ a → κ b → a ≠ b → ¬ Exists (inter a b)) ∧ ¬ κ empty := Iff.rfl
theorem star_84_132 (κ : Family α) : NonemptyExclusive κ ↔
    (∀ ⦃a b⦄, κ a → κ b → Exists (inter a b) → a = b) ∧ ¬ κ empty := by
  rw [star_84_13, star_84_11]
theorem star_84_133 (κ : Family α) (h : NonemptyExclusive κ) :
    ∀ ⦃a⦄, κ a → Exists a := by
  intro a ha
  classical
  by_cases hx : Exists a
  · exact hx
  · have ae : a = empty := by funext x; apply propext; exact ⟨fun hax => (hx ⟨x,hax⟩).elim, False.elim⟩
    exact False.elim (h.2 (ae ▸ ha))
theorem star_84_134 (κ : Family α) : NonemptyExclusive κ ↔
    ∀ ⦃a b⦄, κ a → κ b → Exists a ∧ Exists b ∧ (Exists (inter a b) → a = b) := by
  constructor
  · intro h a b ha hb
    exact ⟨star_84_133 κ h ha, star_84_133 κ h hb, (star_84_11 κ).1 h.1 ha hb⟩
  · intro h; constructor
    · exact (star_84_11 κ).2 (fun {a b} ha hb hi => (h (a := a) (b := b) ha hb).2.2 hi)
    · intro he; exact (h (a := empty) (b := empty) he he).1.elim fun _ hx => hx
theorem star_84_135 (κ : Family α) : NonemptyExclusive κ ↔
    ∀ ⦃a b⦄, κ a → κ b → (Exists (inter a b) ↔ a = b) := by
  constructor
  · intro h a b ha hb; constructor
    · exact (star_84_11 κ).1 h.1 ha hb
    · rintro rfl; rcases star_84_133 κ h ha with ⟨x,hx⟩; exact ⟨x,hx,hx⟩
  · intro h; constructor
    · exact (star_84_11 κ).2 (fun {a b} ha hb hi => (h (a := a) (b := b) ha hb).1 hi)
    · intro he; have hx := (h (a := empty) (b := empty) he he).2 rfl; exact hx.elim fun _ hfalse => hfalse.1
theorem star_84_14 (κ : Family α) : MutuallyExclusive κ ↔ ManyOneMembership κ := by
  rw [star_84_11]; exact ⟨fun h _ _ _ ha hb hxa hxb => h ha hb ⟨_,hxa,hxb⟩,
    fun h _ _ ha hb hi => h ha hb hi.choose_spec.1 hi.choose_spec.2⟩
theorem star_84_2 : NonemptyExclusive (empty : Family α) := by
  exact ⟨fun _ _ ha => ha.elim, fun h => h⟩
theorem star_84_21 (a : Set α) : MutuallyExclusive (singleton a) := by
  intro b c hb hc hn; subst b; subst c; exact (hn rfl).elim
theorem star_84_22 : NonemptyExclusive (units : Family α) := by
  constructor
  · intro a b ha hb hn hi
    rcases ha with ⟨x,hax⟩; rcases hb with ⟨y,hby⟩
    rcases hi with ⟨z,hza,hzb⟩
    apply hn; subst a; subst b
    have e : x = y := hza.symm.trans hzb
    funext t; apply propext; simp [e]
  · intro h; rcases h with ⟨x,h⟩
    have hx := congrFun h x; exact (by simpa [empty] using hx)
theorem star_84_23 (a : Set α) : MutuallyExclusive (singleton a) := star_84_21 a
theorem star_84_24 (a : Set α) (ha : Exists a) : NonemptyExclusive (singleton a) := by
  refine ⟨star_84_23 a, ?_⟩
  intro h; rcases ha with ⟨x,hx⟩
  have he := congrFun h x
  have : ¬ a x := by simpa [empty] using he
  exact this hx

theorem star_84_241 (a : Set α) : NonemptyExclusive (unitImage a) := by
  constructor
  · intro b c hb hc hn hi
    rcases hb with ⟨x,_,hbx⟩; rcases hc with ⟨y,_,hcy⟩
    subst b; subst c; rcases hi with ⟨z,hzx,hzy⟩
    apply hn; funext t; apply propext; simp [hzx.symm.trans hzy]
  · intro h; rcases h with ⟨y,_,hy⟩; have e := congrFun hy y; simpa [empty] using e
theorem star_84_242 (κ : Family α) (hκ : Included κ units) : NonemptyExclusive κ := by
  constructor
  · intro a b ha hb hn hi
    rcases hκ ha with ⟨x,hx⟩; rcases hκ hb with ⟨y,hy⟩; subst a; subst b
    rcases hi with ⟨z,hzx,hzy⟩; apply hn; funext t; apply propext; simp [hzx.symm.trans hzy]
  · intro he; rcases hκ he with ⟨x,hx⟩; have := congrFun hx x; simpa [empty] using this
theorem star_84_25 (κ lam : Family α) (hκ : MutuallyExclusive κ) (hl : Included lam κ) :
    MutuallyExclusive lam := fun _ _ ha hb => hκ (hl ha) (hl hb)
theorem star_84_26 (κ lam : Family α) (hκ : NonemptyExclusive κ) (hl : Included lam κ) :
    NonemptyExclusive lam := ⟨star_84_25 κ lam hκ.1 hl, fun he => hκ.2 (hl he)⟩
theorem star_84_28 (κ lam γ δ : Family α) (h : ClassExcl γ κ)
    (hl : Included lam κ) (hg : Included γ δ) : ClassExcl δ lam :=
  ⟨star_84_25 κ lam h.1 hl, fun _ hx => hg (h.2 (hl hx))⟩
theorem star_84_3 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) : ManyOneRel R := by
  intro x a b ha hb
  exact (star_84_14 κ).1 hκ (hR.1 ha).1 (hR.1 hb).1 (hR.1 ha).2 (hR.1 hb).2
theorem star_84_31 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) {x} (hx : Domain R x) : Unique (fun a => R x a) := by
  rcases hx with ⟨a,ha⟩; exact ⟨a,ha,fun b hb => (star_84_3 κ hκ R hR hb ha)⟩
theorem star_84_32 (κ : Family α) (R : Rel α) (hR : Selects κ R) {x a}
    (h : R x a) : a x ∧ κ a := ⟨(hR.1 h).2,(hR.1 h).1⟩
theorem star_84_33 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) {x} (hx : Domain R x) :
    Unique (fun a => κ a ∧ a x) := by
  rcases hx with ⟨a,ha⟩; refine ⟨a,⟨(hR.1 ha).1,(hR.1 ha).2⟩,?_⟩
  intro b hb; exact (star_84_14 κ).1 hκ hb.1 (hR.1 ha).1 hb.2 (hR.1 ha).2
theorem star_84_34 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) {x a} : R x a ↔ Domain R x ∧ a x ∧ κ a := by
  constructor
  · intro h; exact ⟨⟨a,h⟩,(hR.1 h).2,(hR.1 h).1⟩
  · rintro ⟨⟨b,hb⟩,hax,haκ⟩
    have e := (star_84_14 κ).1 hκ (hR.1 hb).1 haκ (hR.1 hb).2 hax
    exact e ▸ hb
theorem star_84_341 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) : R = fun x a => Domain R x ∧ a x ∧ κ a := by
  funext x a; apply propext; exact star_84_34 κ hκ R hR
theorem star_84_342 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) {a} (ha : κ a) :
    (fun x => R x a) = fun x => a x ∧ Domain R x := by
  funext x; apply propext; rw [star_84_34 κ hκ R hR]; simp [ha, and_comm]
theorem star_84_35 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α) :
    Selects κ R ↔ ManyOneRel R ∧ (∀ ⦃x a⦄, R x a → κ a ∧ a x) ∧
      (∀ ⦃a⦄, κ a → Unique (fun x => R x a)) := by
  exact ⟨fun h => ⟨star_84_3 κ hκ R h,h.1,h.2⟩, fun h => ⟨h.2.1,h.2.2⟩⟩
theorem star_84_37 (κ : Family α) (hκ : MutuallyExclusive κ) (R : Rel α)
    (hR : Selects κ R) : NonemptyExclusive κ := by
  refine ⟨hκ,?_⟩; intro he; rcases hR.2 he with ⟨x,hx,_⟩; exact (hR.1 hx).2
theorem star_84_4 (κ : Family α) (hκ : MutuallyExclusive κ) (R S : Rel α)
    (hR : Selects κ R) (hS : Selects κ S) : Domain R = Domain S ↔ R = S := by
  constructor
  · intro hd; funext x a; apply propext
    rw [star_84_34 κ hκ R hR, star_84_34 κ hκ S hS, hd]
  · rintro rfl; rfl

theorem star_84_41 (κ : Family α) (hκ : MutuallyExclusive κ) (R S : Rel α)
    (hR : Selects κ R) (hS : Selects κ S) : Domain R = Domain S ↔ R = S :=
  star_84_4 κ hκ R S hR hS
theorem star_84_411 (κ : Family α) (mu : Set α) (hh : HitsOnce κ mu)
    (hc : Included mu (sum κ)) : SelectedDomains κ mu := by
  let R : Rel α := fun x a => mu x ∧ a x ∧ κ a
  refine ⟨R, ⟨?_,?_⟩,?_⟩
  · intro x a h; exact ⟨h.2.2,h.2.1⟩
  · intro a ha; rcases hh ha with ⟨x,⟨hm,haX⟩,hu⟩
    exact ⟨x,⟨hm,haX,ha⟩,fun y hy => hu y ⟨hy.1,hy.2.1⟩⟩
  · funext x; apply propext; constructor
    · intro hm; rcases hc hm with ⟨a,ha,hax⟩; exact ⟨a,hm,hax,ha⟩
    · rintro ⟨a,hm,_,_⟩; exact hm
theorem star_84_412 (κ : Family α) (hκ : MutuallyExclusive κ) (mu : Set α) :
    SelectedDomains κ mu ↔ HitsOnce κ mu ∧ Included mu (sum κ) := by
  constructor
  · rintro ⟨R,hR,rfl⟩; constructor
    · intro a ha; rcases hR.2 ha with ⟨x,hx,hu⟩
      exact ⟨x,⟨⟨a,hx⟩,(hR.1 hx).2⟩,fun y hy => hu y ((star_84_34 κ hκ R hR).2 ⟨hy.1,hy.2,ha⟩)⟩
    · rintro x ⟨a,hxa⟩; exact ⟨a,(hR.1 hxa).1,(hR.1 hxa).2⟩
  · rintro ⟨hh,hc⟩; exact star_84_411 κ mu hh hc
theorem star_84_42 (κ : Family α) (hκ : MutuallyExclusive κ) (a mu : Set α)
    (ha : κ a) (hm : SelectedDomains κ mu) : SelectedDomains (familyDiff κ a) (setDiff mu a) := by
  rw [star_84_412 κ hκ mu] at hm
  apply star_84_411
  · intro b hb; rcases hm.1 hb.1 with ⟨x,⟨hmx,hbx⟩,hu⟩
    have hna : ¬ a x := fun hax => hb.2 ((star_84_11 κ).1 hκ hb.1 ha ⟨x,hbx,hax⟩)
    exact ⟨x,⟨⟨hmx,hna⟩,hbx⟩,fun y hy => hu y ⟨hy.1.1,hy.2⟩⟩
  · intro x hx; rcases hm.2 hx.1 with ⟨b,hb,hbx⟩
    exact ⟨b,⟨hb,fun e => hx.2 (e ▸ hbx)⟩,hbx⟩
theorem star_84_421 (κ : Family α) (a mu : Set α) (x : α)
    (hκ : MutuallyExclusive κ) (ha : κ a) (hx : a x) (hm : SelectedDomains (familyDiff κ a) mu)
    (hna : ¬ mu x) : HitsOnce κ (fun y => mu y ∨ y = x) := by
  intro b hb
  by_cases e : b = a
  · subst b; exact ⟨x,⟨Or.inr rfl,hx⟩,fun y hy => by
      rcases hy.1 with hmy|rfl
      · have hfd : MutuallyExclusive (familyDiff κ a) := star_84_25 κ _ hκ (fun _ h => h.1)
        have hc := (star_84_412 _ hfd mu).1 hm |>.2 hmy
        rcases hc with ⟨c,hc,hca⟩
        exact False.elim (hc.2 ((star_84_11 κ).1 hκ hc.1 ha ⟨y,hca,hy.2⟩))
      · rfl⟩
  · have hfd : MutuallyExclusive (familyDiff κ a) := star_84_25 κ _ hκ (fun _ h => h.1)
    rcases ((star_84_412 _ hfd mu).1 hm).1 ⟨hb,e⟩ with ⟨y,⟨hmy,hby⟩,hu⟩
    refine ⟨y,⟨Or.inl hmy,hby⟩,?_⟩
    intro z hz; rcases hz.1 with hmz|rfl
    · exact hu z ⟨hmz,hz.2⟩
    · exact False.elim (e ((star_84_11 κ).1 hκ hb ha ⟨z,hz.2,hx⟩))
theorem star_84_422 (κ : Family α) (hκ : MutuallyExclusive κ) (a mu : Set α) :
    SelectedDomains (familyDiff κ a) (setDiff mu a) ↔
      HitsOnce (familyDiff κ a) (setDiff mu a) ∧ Included (setDiff mu a) (sum (familyDiff κ a)) := by
  exact star_84_412 _ (star_84_25 κ _ hκ (fun _ h => h.1)) _
theorem star_84_43 (κ lam : Family α) (hκ : MutuallyExclusive κ)
    (hl : MutuallyExclusive lam) (hs : sum κ = sum lam) :
    CrossSelectable κ lam ↔ CrossSelectable lam κ := by
  constructor
  · intro h b hb
    apply (star_84_412 κ hκ b).2; constructor
    · intro a ha
      have sa := (star_84_412 lam hl a).1 (h ha)
      rcases sa.1 hb with ⟨x,⟨hax,hbx⟩,hu⟩
      exact ⟨x,⟨hbx,hax⟩,fun y hy => hu y ⟨hy.2,hy.1⟩⟩
    · intro x hbx; rw [hs]; exact ⟨b,hb,hbx⟩
  · intro h a ha
    apply (star_84_412 lam hl a).2; constructor
    · intro b hb
      have sb := (star_84_412 κ hκ b).1 (h hb)
      rcases sb.1 ha with ⟨x,⟨hbx,hax⟩,hu⟩
      exact ⟨x,⟨hax,hbx⟩,fun y hy => hu y ⟨hy.2,hy.1⟩⟩
    · intro x hax; rw [← hs]; exact ⟨a,ha,hax⟩
theorem star_84_51 (R : α → α → Prop) (κ : Family α) (hi : ImageInjective R)
    (hκ : MutuallyExclusive κ) : MutuallyExclusive (imageFamily R κ) := by
  intro c d hc hd hn ⟨y,hcy,hdy⟩
  rcases hc with ⟨a,ha,rfl⟩; rcases hd with ⟨b,hb,rfl⟩
  rcases hcy with ⟨x,hax,hxy⟩; rcases hdy with ⟨z,hbz,hzy⟩
  have e : x = z := hi hxy hzy; subst z
  exact hκ ha hb (fun eab => hn (eab ▸ rfl)) ⟨x,hax,hbz⟩
theorem star_84_52 (R : α → α → Prop) (κ : Family α) (hi : ImageInjective R)
    (hκ : MutuallyExclusive κ) : MutuallyExclusive (imageFamily R κ) := star_84_51 R κ hi hκ
theorem star_84_521 (R : α → α → Prop) (κ : Family α)
    (h : ImageInjective R ∧ MutuallyExclusive κ) : MutuallyExclusive (imageFamily R κ) :=
  star_84_51 R κ h.1 h.2
theorem star_84_522 (R : α → α → Prop) (κ : Family α)
    (hi : ImageInjective R) (hκ : MutuallyExclusive κ) :
    MutuallyExclusive (imageFamily R κ) ↔ MutuallyExclusive (imageFamily R κ) := Iff.rfl
theorem star_84_53 (R : α → α → Prop) (κ : Family α) (hi : ImageInjective R)
    (hκ : MutuallyExclusive κ) : MutuallyExclusive (imageFamily R κ) := star_84_51 R κ hi hκ
theorem star_84_54 (R : α → α → Prop) (κ : Family α)
    (hi : ImageInjective (fun x y => R y x)) (hκ : MutuallyExclusive κ) :
    MutuallyExclusive (imageFamily (fun x y => R y x) κ) := star_84_51 _ κ hi hκ
theorem star_84_55 (a : Set α) : MutuallyExclusive (unitImage a) := (star_84_241 a).1
theorem star_84_59 (κ lam : Family α) : MutuallyExclusive (familyUnion κ lam) ↔
    MutuallyExclusive κ ∧ MutuallyExclusive lam ∧ CrossDisjoint κ lam ∧ CrossDisjoint lam κ := by
  constructor
  · intro h; exact ⟨fun _ _ ha hb => h (Or.inl ha) (Or.inl hb),
      fun _ _ ha hb => h (Or.inr ha) (Or.inr hb),
      fun _ _ ha hb => h (Or.inl ha) (Or.inr hb),
      fun _ _ ha hb => h (Or.inr ha) (Or.inl hb)⟩
  · rintro ⟨hk,hl,hkl,hlk⟩ a b (ha|ha) (hb|hb)
    · exact hk ha hb
    · exact hkl ha hb
    · exact hlk ha hb
    · exact hl ha hb
theorem star_84_6 (κ lam : Family α) : MutuallyExclusive (familyUnion κ lam) ↔
    MutuallyExclusive κ ∧ MutuallyExclusive lam ∧ CrossDisjoint κ lam ∧ CrossDisjoint lam κ :=
  star_84_59 κ lam
theorem star_84_61 (κ : Family α) (b : Set α) (hb : ¬ κ b) :
    MutuallyExclusive (familyUnion κ (singleton b)) ↔
      MutuallyExclusive κ ∧ (∀ ⦃a⦄, κ a → ¬ Exists (inter a b)) := by
  constructor
  · intro h; constructor
    · intro a c ha hc; exact h (Or.inl ha) (Or.inl hc)
    · intro a ha hi; exact h (Or.inl ha) (Or.inr rfl) (fun e => hb (e ▸ ha)) hi
  · rintro ⟨hκ,hcross⟩
    rw [star_84_59]; refine ⟨hκ,star_84_23 b,?_,?_⟩
    · intro a c ha hc hn; subst c; exact hcross ha
    · intro c a hc ha hn; subst c; intro hi
      exact hcross ha ⟨hi.choose,hi.choose_spec.2,hi.choose_spec.1⟩
theorem star_84_62 (a b : Set α) (hne : a ≠ b) :
    MutuallyExclusive (familyUnion (singleton a) (singleton b)) ↔
      ¬ Exists (inter a b) := by
  constructor
  · intro h; exact h (Or.inl rfl) (Or.inr rfl) hne
  · intro hd; apply (star_84_59 _ _).2
    refine ⟨star_84_23 a,star_84_23 b,?_,?_⟩
    · intro c d hc hd' _; subst c; subst d; exact hd
    · intro d c hd' hc _; subst c; subst d; intro hi
      exact hd ⟨hi.choose,hi.choose_spec.2,hi.choose_spec.1⟩
end PM.Architecture.Star84Kernel
