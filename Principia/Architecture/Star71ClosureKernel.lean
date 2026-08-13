import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71ClosureKernel
open PM.Architecture.Star71OpeningKernel
universe u
abbrev Rel (α : Sort u) := α → α → Prop
def Included (R S : Rel α) := ∀ x y, R x y → S x y
def Inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y
def Union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def DisjointDomain (R S : Rel α) := ∀ x, ¬ ((∃ y, R x y) ∧ ∃ y, S x y)
def DisjointCodomain (R S : Rel α) := ∀ y, ¬ ((∃ x, R x y) ∧ ∃ x, S x y)
def DisjointField (R S : Rel α) := ∀ x,
  ¬ (((∃ y, R x y) ∨ ∃ y, R y x) ∧ ((∃ y, S x y) ∨ ∃ y, S y x))

/-- PM I ✱71·2, the three converse-image identities. -/
theorem star_71_2 (R : Rel α) :
    (ManyOne R ↔ OneMany (converse R)) ∧
    (OneMany R ↔ ManyOne (converse R)) ∧
    (OneOne R ↔ OneOne (converse R)) := by
  constructor
  · constructor <;> intro h <;> intro x y z hx hy <;> exact h hx hy
  · constructor
    · constructor <;> intro h <;> intro x y z hx hy <;> exact h hx hy
    · constructor
      · rintro ⟨hi,hf⟩; constructor
        · intro x y z hx hy; exact hf hx hy
        · intro x y z hx hy; exact hi hx hy
      · rintro ⟨hi,hf⟩; constructor
        · intro x y z hx hy; exact hf hx hy
        · intro x y z hx hy; exact hi hx hy
/-- PM I ✱71·21. -/
theorem star_71_21 (R : Rel α) : OneMany R ↔ ManyOne (converse R) := by
  constructor <;> intro h <;> intro x y z hy hz <;> exact h hy hz
/-- PM I ✱71·211. -/
theorem star_71_211 (R : Rel α) : ManyOne R ↔ OneMany (converse R) := by
  constructor <;> intro h <;> intro x y z hx hy <;> exact h hx hy
/-- PM I ✱71·212. -/
theorem star_71_212 (R : Rel α) : OneOne R ↔ OneOne (converse R) := by
  constructor
  · rintro ⟨hi,hf⟩; exact ⟨(star_71_211 R).mp hf,(star_71_21 R).mp hi⟩
  · rintro ⟨hi,hf⟩; exact ⟨(star_71_21 R).mpr hf,(star_71_211 R).mpr hi⟩
/-- PM I ✱71·22. -/
theorem star_71_22 (R S : Rel α) (hR : OneMany R) (hSR : Included S R) : OneMany S :=
  fun ⦃x y z⦄ hx hy => hR (hSR x z hx) (hSR y z hy)
/-- PM I ✱71·221. -/
theorem star_71_221 (R S : Rel α) (hR : ManyOne R) (hSR : Included S R) : ManyOne S :=
  fun ⦃x y z⦄ hy hz => hR (hSR x y hy) (hSR x z hz)
/-- PM I ✱71·222. -/
theorem star_71_222 (R S : Rel α) (hR : OneOne R) (hSR : Included S R) : OneOne S :=
  ⟨star_71_22 R S hR.1 hSR,star_71_221 R S hR.2 hSR⟩
/-- PM I ✱71·223. -/
theorem star_71_223 (R : Rel α) (hR : OneMany R) : ∀ S, Included S R → OneMany S := fun S => star_71_22 R S hR
/-- PM I ✱71·224. -/
theorem star_71_224 (R : Rel α) (hR : ManyOne R) : ∀ S, Included S R → ManyOne S := fun S => star_71_221 R S hR
/-- PM I ✱71·225. -/
theorem star_71_225 (R : Rel α) (hR : OneOne R) : ∀ S, Included S R → OneOne S := fun S => star_71_222 R S hR
/-- PM I ✱71·23. -/
theorem star_71_23 (R S : Rel α) (hR : OneMany R) : OneMany (Inter R S) :=
  star_71_22 R _ hR (fun _ _ h => h.1)
/-- PM I ✱71·231. -/
theorem star_71_231 (R S : Rel α) (hR : ManyOne R) : ManyOne (Inter R S) :=
  star_71_221 R _ hR (fun _ _ h => h.1)
/-- PM I ✱71·232. -/
theorem star_71_232 (R S : Rel α) (hR : OneOne R) : OneOne (Inter R S) :=
  star_71_222 R _ hR (fun _ _ h => h.1)
/-- PM I ✱71·233. -/
theorem star_71_233 (R S : Rel α) (hR : OneMany R) (hS : OneMany S) : OneOne (Inter R (converse S)) :=
  ⟨fun ⦃x y z⦄ hx hy => hR hx.1 hy.1,
   fun ⦃x y z⦄ hx hy => ((star_71_21 S).mp hS) hx.2 hy.2⟩
/-- PM I ✱71·234. -/
theorem star_71_234 (R S : Rel α) (hR : ManyOne R) (hS : ManyOne S) : OneOne (Inter R (converse S)) :=
  ⟨fun ⦃x y z⦄ hx hy => ((star_71_211 S).mp hS) hx.2 hy.2,
   fun ⦃x y z⦄ hx hy => hR hx.1 hy.1⟩
/-- PM I ✱71·235. -/
theorem star_71_235 (R S : Rel α) (hR : OneMany R) (hS : ManyOne S) : OneOne (Inter R S) :=
  ⟨fun ⦃x y z⦄ hx hy => hR hx.1 hy.1,
   fun ⦃x y z⦄ hx hy => hS hx.2 hy.2⟩
/-- PM I ✱71·24. -/
theorem star_71_24 (R S : Rel α) (hR : OneMany R) (hS : OneMany S) (hd : DisjointCodomain R S) : OneMany (Union R S) := by
  intro x y z hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact hR hx hy
  · exact (hd z ⟨⟨x,hx⟩,⟨y,hy⟩⟩).elim
  · exact (hd z ⟨⟨y,hy⟩,⟨x,hx⟩⟩).elim
  · exact hS hx hy
/-- PM I ✱71·241. -/
theorem star_71_241 (R S : Rel α) (hR : ManyOne R) (hS : ManyOne S) (hd : DisjointDomain R S) : ManyOne (Union R S) := by
  intro x y z hy hz
  rcases hy with hy|hy <;> rcases hz with hz|hz
  · exact hR hy hz
  · exact (hd x ⟨⟨y,hy⟩,⟨z,hz⟩⟩).elim
  · exact (hd x ⟨⟨z,hz⟩,⟨y,hy⟩⟩).elim
  · exact hS hy hz
/-- PM I ✱71·242. -/
theorem star_71_242 (R S : Rel α) (hR : OneOne R) (hS : OneOne S)
    (hd : DisjointDomain R S) (hc : DisjointCodomain R S) : OneOne (Union R S) :=
  ⟨star_71_24 R S hR.1 hS.1 hc,star_71_241 R S hR.2 hS.2 hd⟩
/-- PM I ✱71·243. -/
theorem star_71_243 (R S : Rel α) (hR : OneOne R) (hS : OneOne S)
    (hf : DisjointField R S) : OneOne (Union R S) := by
  apply star_71_242 R S hR hS
  · intro x h; exact hf x ⟨Or.inl h.1,Or.inl h.2⟩
  · intro x h; exact hf x ⟨Or.inr h.1,Or.inr h.2⟩

end PM.Architecture.Star71ClosureKernel
