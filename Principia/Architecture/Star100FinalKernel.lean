import Principia.Architecture.Star100SecondKernel

namespace PM.Architecture.Star100FinalKernel
open Star100OpeningKernel

def Image (f : α → α) (a : Class α) : Class α := fun y => ∃ x, a x ∧ f x = y

noncomputable def imageEquivOfInjective (f : α → α) (a : Class α) (hf : ∀ x y, f x = f y → x = y) :
    ClassEquiv a (Image f a) where
  toFun x := ⟨f x, x, x.property, rfl⟩
  invFun y := ⟨Classical.choose y.property, (Classical.choose_spec y.property).1⟩
  leftInv x := by
    apply Subtype.eq
    exact hf _ _ (Classical.choose_spec (show Image f a (f x) from ⟨x, x.property, rfl⟩)).2
  rightInv y := by
    apply Subtype.eq
    exact (Classical.choose_spec y.property).2

theorem image_similar (f : α → α) (a : Class α) (hf : ∀ x y, f x = f y → x = y) :
    Similar (Image f a) a := by
  let e := imageEquivOfInjective f a hf
  exact ⟨⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩⟩

theorem star_100_6 (f : α → α) (a : Class α) (hf : ∀ x y, f x = f y → x = y) :
    Similar (Image f a) a := image_similar f a hf

theorem star_100_61 (pairWith : α → α) (a : Class α)
    (hinj : ∀ x y, pairWith x = pairWith y → x = y) : Similar (Image pairWith a) a :=
  image_similar pairWith a hinj

theorem star_100_62 (down : α → α) (a : Class α)
    (hinj : ∀ x y, down x = down y → x = y) : Similar (Image down a) a :=
  image_similar down a hinj

theorem star_100_621 (down : α → α) (a : Class α)
    (hinj : ∀ x y, down x = down y → x = y) : Similar (Image down a) a :=
  image_similar down a hinj

theorem star_100_63 (diag : α → α) (a : Class α)
    (hinj : ∀ x y, diag x = diag y → x = y) : Similar (Image diag a) a :=
  image_similar diag a hinj

theorem star_100_631 (dom : α → α) (a : Class α)
    (hinj : ∀ x y, dom x = dom y → x = y) : Similar (Image dom a) a :=
  image_similar dom a hinj

def PairwiseDisjoint (k : Class (Class α)) :=
  ∀ a b, k a → k b → (∃ x, a x ∧ b x) → a = b

theorem common_member_identifies {k : Class (Class α)} (hd : PairwiseDisjoint k)
    {a b : Class α} (ha : k a) (hb : k b) (x : α) (hxa : a x) (hxb : b x) : a = b :=
  hd a b ha hb ⟨x, hxa, hxb⟩

def DomainBundle (k : Class (Class α)) (a : Class α) : Class (Class α) :=
  fun b => ∃ x, a x ∧ k b ∧ b x

theorem domainBundle_included (k : Class (Class α)) (a : Class α) :
    ∀ b, DomainBundle k a b → k b := by rintro b ⟨_, _, hb, _⟩; exact hb

theorem star_100_64 (k : Class (Class α)) (hd : PairwiseDisjoint k)
    (domains : Class (Class (Class α)))
    (hsim : ∀ d, domains d → Similar d k) : ∀ d, domains d → Nc k d := by
  intro d hdmem
  exact hsim d hdmem

end PM.Architecture.Star100FinalKernel
