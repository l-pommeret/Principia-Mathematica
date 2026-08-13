import Principia.Architecture.Star71OpeningKernel
import Principia.Architecture.Star71ClosureKernel

namespace PM.Architecture.Star71OperationsKernel
open PM.Architecture.Star71OpeningKernel
open PM.Architecture.Star71ClosureKernel
universe u

def domain (R : Rel α) : Class α := fun x => ∃ y, R x y
def codomain (R : Rel α) : Class α := fun y => ∃ x, R x y
def leftRestriction (a : Class α) (R : Rel α) : Rel α := fun x y => a x ∧ R x y
def rightRestriction (R : Rel α) (a : Class α) : Rel α := fun x y => R x y ∧ a y
def bothRestrictions (a : Class α) (R : Rel α) (b : Class α) : Rel α := fun x y => a x ∧ R x y ∧ b y
def comp (R S : Rel α) : Rel α := fun x z => ∃ y, R x y ∧ S y z

/-- PM I ✱71·244. -/
theorem star_71_244 (R S : Rel α) (hR : OneMany R) (hS : OneMany S)
    (h : Included (rightRestriction R (codomain S)) S) : OneMany (Union R S) := by
  intro x y z hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact hR hx hy
  · exact hS (h _ _ ⟨hx,⟨y,hy⟩⟩) hy
  · exact (hS (h _ _ ⟨hy,⟨x,hx⟩⟩) hx).symm
  · exact hS hx hy
/-- PM I ✱71·245. -/
theorem star_71_245 (R S : Rel α) (hR : ManyOne R) (hS : ManyOne S)
    (h : Included (leftRestriction (domain S) R) S) : ManyOne (Union R S) := by
  intro x y z hy hz
  rcases hy with hy|hy <;> rcases hz with hz|hz
  · exact hR hy hz
  · exact hS (h _ _ ⟨⟨z,hz⟩,hy⟩) hz
  · exact (hS (h _ _ ⟨⟨y,hy⟩,hz⟩) hy).symm
  · exact hS hy hz
/-- PM I ✱71·25. -/
theorem star_71_25 (R S : Rel α) (hR : OneMany R) (hS : OneMany S) : OneMany (comp R S) := by
  rintro x y z ⟨w,hx,hw⟩ ⟨v,hy,hv⟩
  have : w = v := hS hw hv
  subst v; exact hR hx hy
/-- PM I ✱71·251. -/
theorem star_71_251 (R S : Rel α) (hR : ManyOne R) (hS : ManyOne S) : ManyOne (comp R S) := by
  rintro x y z ⟨w,hw,hy⟩ ⟨v,hv,hz⟩
  have : w = v := hR hw hv
  subst v; exact hS hy hz
/-- PM I ✱71·252. -/
theorem star_71_252 (R S : Rel α) (hR : OneOne R) (hS : OneOne S) : OneOne (comp R S) :=
  ⟨star_71_25 R S hR.1 hS.1,star_71_251 R S hR.2 hS.2⟩
/-- PM I ✱71·26. -/
theorem star_71_26 (R : Rel α) (a : Class α) (hR : OneMany R) : OneMany (rightRestriction R a) :=
  star_71_22 R _ hR (fun _ _ h => h.1)
/-- PM I ✱71·261. -/
theorem star_71_261 (R : Rel α) (a : Class α) (hR : ManyOne R) : ManyOne (leftRestriction a R) :=
  star_71_221 R _ hR (fun _ _ h => h.2)
/-- PM I ✱71·27. -/
theorem star_71_27 (R : Rel α) (a : Class α) (hR : OneMany R) : OneMany (leftRestriction a R) :=
  star_71_22 R _ hR (fun _ _ h => h.2)
/-- PM I ✱71·271. -/
theorem star_71_271 (R : Rel α) (a : Class α) (hR : ManyOne R) : ManyOne (rightRestriction R a) :=
  star_71_221 R _ hR (fun _ _ h => h.1)
/-- PM I ✱71·28. -/
theorem star_71_28 (R : Rel α) (a b : Class α) (hR : OneMany R) : OneMany (bothRestrictions a R b) :=
  star_71_22 R _ hR (fun _ _ h => h.2.1)
/-- PM I ✱71·281. -/
theorem star_71_281 (R : Rel α) (a b : Class α) (hR : ManyOne R) : ManyOne (bothRestrictions a R b) :=
  star_71_221 R _ hR (fun _ _ h => h.2.1)
/-- PM I ✱71·29, retaining its three printed conclusions. -/
theorem star_71_29 (R : Rel α) (a b : Class α) (hR : OneOne R) :
    OneOne (leftRestriction a R) ∧ OneOne (rightRestriction R b) ∧ OneOne (bothRestrictions a R b) :=
  ⟨⟨star_71_27 R a hR.1,star_71_261 R a hR.2⟩,
   ⟨star_71_26 R b hR.1,star_71_271 R b hR.2⟩,
   star_71_222 R _ hR (fun _ _ h => h.2.1)⟩
/-- PM I ✱71·31. -/
theorem star_71_31 (R : Rel α) (pick : α → α) (hR : OneMany R)
    (hpick : ∀ y, codomain R y → R (pick y) y) (y : α) (hy : codomain R y) : R (pick y) y := hpick y hy
/-- PM I ✱71·311. -/
theorem star_71_311 (R : Rel α) (pick : α → α) (hR : ManyOne R)
    (hpick : ∀ x, domain R x → R x (pick x)) (x : α) (hx : domain R x) : R x (pick x) := hpick x hx
/-- PM I ✱71·312. -/
theorem star_71_312 (R : Rel α) (f g : α → α) (hR : OneOne R)
    (hf : ∀ x, domain R x → R x (f x)) (hg : ∀ y, codomain R y → R (g y) y)
    (x y : α) (hx : domain R x) (hy : codomain R y) : R x (f x) ∧ R (g y) y := ⟨hf x hx,hg y hy⟩

end PM.Architecture.Star71OperationsKernel
