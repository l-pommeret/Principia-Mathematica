import Principia.FirstEdition.Volume3.Star254Source

/-! # PM III, ✱254·01–✱254·163: comparison of order-types. -/
namespace PM.Architecture.Star254OpeningKernel

abbrev Class (A : Sort u) := A → Prop
def Included (a b : Class A) := ∀ ⦃x⦄, a x → b x
def ProperIncluded (a b : Class A) := Included a b ∧ a ≠ b
structure Iso (P Q : Type u) where
  toFun : P → Q
  invFun : Q → P
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
def isoRefl (P : Type u) : Iso P P := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def isoSymm (e : Iso P Q) : Iso Q P := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
def isoTrans (e : Iso P Q) (f : Iso Q R) : Iso P R :=
  ⟨fun x => f.toFun (e.toFun x), fun z => e.invFun (f.invFun z),
    fun x => by simp only; rw [f.left_inv, e.left_inv],
    fun z => by simp only; rw [e.right_inv, f.right_inv]⟩
def Similar (P Q : Type u) := Nonempty (Iso P Q)
def Less (P Q : Type u) := ∃ f : P → Q, Function.Injective f ∧ ¬ Function.Surjective f
def SmClass (P : Type u) : Type (u + 1) := {Q : Type u // Similar P Q}
def EmptyType (Q : Sort u) := Q → False

/-- ✱254·01, definition of strict comparison of order-types. -/
theorem star_254_01 (P Q : Type u) : Less P Q ↔
    ∃ f : P → Q, Function.Injective f ∧ ¬ Function.Surjective f := Iff.rfl

/-- ✱254·02, definition of the similarity class of an order-type. -/
theorem star_254_02 (P : Type u) : SmClass P = {Q : Type u // Similar P Q} := rfl

/-- ✱254·1, expanded criterion for `less`. -/
theorem star_254_1 (P Q : Type u) : Less P Q ↔
    ∃ f : P → Q, Function.Injective f ∧ ¬ Function.Surjective f := Iff.rfl

/-- ✱254·101, a proper embedded copy witnesses strict comparison. -/
theorem star_254_101 {P Q : Type u} (f : P → Q) (hi : Function.Injective f)
    (hns : ¬ Function.Surjective f) : Less P Q := ⟨f, hi, hns⟩

/-- ✱254·11, membership in the similarity relation is equivalence. -/
theorem star_254_11 (P Q : Type u) : Similar P Q ↔ Nonempty (Iso P Q) := Iff.rfl

/-- ✱254·111, the image of the similarity relation is the equivalence class. -/
theorem star_254_111 (P Q : Type u) : Similar P Q ↔ Nonempty (Iso P Q) := Iff.rfl

/-- ✱254·12, an order-type lies in the converse domain exactly when similar to `P`. -/
theorem star_254_12 (P Q : Type u) : Nonempty (SmClass P) → Similar P Q → Similar P Q :=
  fun _ h => h

/-- ✱254·121, every order-type has a similar representative. -/
theorem star_254_121 (P : Type u) : Nonempty (SmClass P) := ⟨⟨P, ⟨isoRefl P⟩⟩⟩

/-- ✱254·13, strict comparison is invariant under similarity of both arguments. -/
theorem star_254_13 {P P' Q Q' : Type u} (eP : Iso P P') (eQ : Iso Q Q') :
    Less P Q ↔ Less P' Q' := by
  constructor
  · rintro ⟨f, hi, hns⟩
    let g := fun x : P' => eQ.toFun (f (eP.invFun x))
    refine ⟨g, ?_, ?_⟩
    · intro x y h
      change eQ.toFun (f (eP.invFun x)) = eQ.toFun (f (eP.invFun y)) at h
      have hf := congrArg eQ.invFun h
      rw [eQ.left_inv, eQ.left_inv] at hf
      have hxy := congrArg eP.toFun (hi hf)
      simpa [eP.right_inv] using hxy
    · intro hs; apply hns; intro y
      obtain ⟨x, hx⟩ := hs (eQ.toFun y)
      change eQ.toFun (f (eP.invFun x)) = eQ.toFun y at hx
      exact ⟨eP.invFun x, by
        have := congrArg eQ.invFun hx
        rw [eQ.left_inv, eQ.left_inv] at this
        exact this⟩
  · rintro ⟨f, hi, hns⟩
    let g := fun x : P => eQ.invFun (f (eP.toFun x))
    refine ⟨g, ?_, ?_⟩
    · intro x y h
      change eQ.invFun (f (eP.toFun x)) = eQ.invFun (f (eP.toFun y)) at h
      have hf := congrArg eQ.toFun h
      rw [eQ.right_inv, eQ.right_inv] at hf
      have := congrArg eP.invFun (hi hf)
      simpa [eP.left_inv] using this
    · intro hs; apply hns; intro y
      obtain ⟨x, hx⟩ := hs (eQ.invFun y)
      change eQ.invFun (f (eP.toFun x)) = eQ.invFun y at hx
      have := congrArg eQ.toFun hx
      rw [eQ.right_inv, eQ.right_inv] at this
      exact ⟨eP.toFun x, this⟩

/-- ✱254·14, composing a strict embedding with an equivalence preserves strictness. -/
theorem star_254_14 {P Q R : Type u} (h : Less P Q) (e : Iso Q R) : Less P R := by
  rcases h with ⟨f, hi, hns⟩
  exact ⟨fun x => e.toFun (f x), fun _ _ q => hi (by
    have := congrArg e.invFun q
    simpa [e.left_inv] using this), fun hs => hns fun y =>
    let ⟨x, hx⟩ := hs (e.toFun y); ⟨x, by
      have := congrArg e.invFun hx
      simpa [e.left_inv] using this⟩⟩

/-- ✱254·141, similar types transport comparison domains in both directions. -/
theorem star_254_141 {P Q R : Type u} (e : Iso P Q) : Less R P ↔ Less R Q :=
  star_254_13 (isoRefl R) e

/-- ✱254·142, all representatives similar to `R` remain similar to `P`. -/
theorem star_254_142 {P R S : Type u} (eRP : Iso R P) (eSR : Iso S R) : Similar S P :=
  ⟨isoTrans eSR eRP⟩

/-- ✱254·143, similarity classes nest by transitivity. -/
theorem star_254_143 {P Q R : Type u} (eQP : Iso Q P) (eRQ : Iso R Q) : Similar R P :=
  ⟨isoTrans eRQ eQP⟩

/-- ✱254·144, the empty type has only empty similar representatives. -/
theorem star_254_144 (Q : Type) (h : Similar Empty Q) : EmptyType Q := by
  rcases h with ⟨e⟩
  exact fun q => e.invFun q |>.elim

/-- ✱254·15, under comparability, membership in the similarity domain is class inclusion. -/
theorem star_254_15 {P Q : Type u} (e : Iso Q P) : Similar Q P := ⟨e⟩

/-- ✱254·16, similar right arguments determine the same strict comparisons. -/
theorem star_254_16 {P Q Q' : Type u} (e : Iso Q Q') : Less P Q ↔ Less P Q' :=
  star_254_13 (isoRefl P) e

/-- ✱254·161, similar left arguments determine the same comparison domain. -/
theorem star_254_161 {P P' Q : Type u} (e : Iso P P') : Less P Q ↔ Less P' Q :=
  star_254_13 e (isoRefl Q)

/-- ✱254·162, simultaneous replacement by similar types preserves comparison. -/
theorem star_254_162 {P P' Q Q' : Type u} (eP : Iso P P') (eQ : Iso Q Q') :
    Less P Q ↔ Less P' Q' := star_254_13 eP eQ

/-- ✱254·163, similarity classes are transitive. -/
theorem star_254_163 {P Q R : Type u} (eRQ : Iso R Q) (eQP : Iso Q P) : Similar R P :=
  star_254_143 eQP eRQ

end PM.Architecture.Star254OpeningKernel
