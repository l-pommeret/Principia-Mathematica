import Principia.Architecture.Star71OpeningKernel

namespace PM.Architecture.Star71UniquenessKernel
open PM.Architecture.Star71OpeningKernel
universe u v

def ExistsUniqueIn (a : Class α) : Prop := ∃ x, a x ∧ ∀ y, a y → y = x
def domain (R : Relation α β) : Class α := fun x => ∃ y, R x y
def codomain (R : Relation α β) : Class β := fun y => ∃ x, R x y
def comp (R : Relation α β) (S : Relation β γ) : Relation α γ := fun x z => ∃ y, R x y ∧ S y z
def identityOn (a : Class α) : Relation α α := fun x y => x = y ∧ a y
def SectionsAtMostOne (F : Class (Class α)) : Prop := ∀ a, F a → AtMostOne a

/-- PM I ✱71·151. -/
theorem star_71_151 (R : Relation α β) : ManyOne R ↔
    SectionsAtMostOne (leftSectionFamily R) := star_71_02 R
/-- PM I ✱71·152. -/
theorem star_71_152 (R : Relation α β) : OneOne R ↔
    SectionsAtMostOne (rightSectionFamily R) ∧ SectionsAtMostOne (leftSectionFamily R) := star_71_03 R
/-- PM I ✱71·16. -/
theorem star_71_16 (R : Relation α β) : OneMany R ↔
    ∀ y, codomain R y → ExistsUniqueIn (rightSection R y) := by
  rw [star_71_1]; constructor
  · intro h y ⟨x,hx⟩; exact ⟨x,hx,fun z hz => h y hz hx⟩
  · intro h y x z hx hz
    rcases h y ⟨x,hx⟩ with ⟨w,hw,hu⟩
    exact (hu x hx).trans (hu z hz).symm
/-- PM I ✱71·161. -/
theorem star_71_161 (R : Relation α β) : ManyOne R ↔
    ∀ x, domain R x → ExistsUniqueIn (leftSection R x) := by
  rw [star_71_101]; constructor
  · intro h x ⟨y,hy⟩; exact ⟨y,hy,fun z hz => h x hz hy⟩
  · intro h x y z hy hz
    rcases h x ⟨y,hy⟩ with ⟨w,hw,hu⟩
    exact (hu y hy).trans (hu z hz).symm
/-- PM I ✱71·162. -/
theorem star_71_162 (R : Relation α β) : OneOne R ↔
    (∀ y, codomain R y → ExistsUniqueIn (rightSection R y)) ∧
    (∀ x, domain R x → ExistsUniqueIn (leftSection R x)) := by rw [OneOne,star_71_16,star_71_161]
/-- PM I ✱71·163. -/
theorem star_71_163 (R : Relation α β) : OneMany R ↔
    ∀ y, codomain R y ↔ ExistsUniqueIn (rightSection R y) := by
  rw [star_71_16]; constructor
  · intro h y; constructor
    · exact h y
    · rintro ⟨x,hx,_⟩; exact ⟨x,hx⟩
  · intro h y hy; exact (h y).mp hy
/-- PM I ✱71·164. -/
theorem star_71_164 (R : Relation α β) : ManyOne R ↔
    ∀ x, domain R x ↔ ExistsUniqueIn (leftSection R x) := by
  rw [star_71_161]; constructor
  · intro h x; exact ⟨h x, fun ⟨y,hy,_⟩ => ⟨y,hy⟩⟩
  · intro h x hx; exact (h x).mp hx
/-- PM I ✱71·165. -/
theorem star_71_165 (R : Relation α β) : OneOne R ↔
    (∀ y, codomain R y ↔ ExistsUniqueIn (rightSection R y)) ∧
    (∀ x, domain R x ↔ ExistsUniqueIn (leftSection R x)) := by rw [OneOne,star_71_163,star_71_164]
/-- PM I ✱71·166. -/
theorem star_71_166 (R : Relation α β)
    (h : ∀ y, ExistsUniqueIn (rightSection R y)) : OneMany R := by
  rw [star_71_1]; intro y x z hx hz
  rcases h y with ⟨w,hw,hu⟩
  exact (hu x hx).trans (hu z hz).symm
/-- PM I ✱71·167. -/
theorem star_71_167 (R : Relation α β)
    (h : ∀ x, ExistsUniqueIn (leftSection R x)) : ManyOne R := by
  rw [star_71_101]; intro x y z hy hz
  rcases h x with ⟨w,hw,hu⟩
  exact (hu y hy).trans (hu z hz).symm
/-- PM I ✱71·168. -/
theorem star_71_168 (R : Relation α β)
    (hr : ∀ y, ExistsUniqueIn (rightSection R y))
    (hl : ∀ x, ExistsUniqueIn (leftSection R x)) : OneOne R := ⟨star_71_166 R hr,star_71_167 R hl⟩
/-- PM I ✱71·17. -/
theorem star_71_17 (R : Relation α β) : OneMany R ↔ ∀ x y z, R x z → R y z → x = y := Iff.rfl
/-- PM I ✱71·171. -/
theorem star_71_171 (R : Relation α β) : ManyOne R ↔ ∀ x y z, R x y → R x z → y = z := Iff.rfl
/-- PM I ✱71·172. -/
theorem star_71_172 (R : Relation α β) : OneOne R ↔
    (∀ x y z, R x z → R y z → x = y) ∧ (∀ x y z, R x y → R x z → y = z) := Iff.rfl
/-- PM I ✱71·18. -/
theorem star_71_18 (R : Relation α β) : OneMany R ↔
    ∀ x y, (∃ z, R x z ∧ R y z) → x = y := by
  constructor
  · rintro h x y ⟨z,hx,hy⟩; exact h hx hy
  · intro h x y z hx hy; exact h x y ⟨z,hx,hy⟩
/-- PM I ✱71·181. -/
theorem star_71_181 (R : Relation α β) : ManyOne R ↔
    ∀ y z, (∃ x, R x y ∧ R x z) → y = z := by
  constructor
  · rintro h y z ⟨x,hy,hz⟩; exact h hy hz
  · intro h x y z hy hz; exact h y z ⟨x,hy,hz⟩
/-- PM I ✱71·182. -/
theorem star_71_182 (R : Relation α α) : OneOne R ↔
    ∀ x y, ((∃ z, R x z ∧ R y z) ∨ (∃ z, R z x ∧ R z y)) → x = y := by
  constructor
  · rintro ⟨hi,hf⟩ x y (⟨z,hx,hy⟩ | ⟨z,hx,hy⟩)
    · exact hi hx hy
    · exact hf hx hy
  · intro h; constructor
    · intro x y z hx hy; exact h x y (Or.inl ⟨z,hx,hy⟩)
    · intro x y z hx hy; exact h y z (Or.inr ⟨x,hx,hy⟩)
/-- PM I ✱71·19. -/
theorem star_71_19 (R : Relation α β) : OneMany R ↔
    comp R (converse R) = identityOn (domain R) := by
  constructor
  · intro h; funext x y; apply propext; constructor
    · rintro ⟨z,hxz,hyz⟩; exact ⟨h hxz hyz,⟨z,hyz⟩⟩
    · rintro ⟨rfl,z,hyz⟩; exact ⟨z,hyz,hyz⟩
  · intro h x y z hx hy; have q : comp R (converse R) x y := ⟨z,hx,hy⟩; exact (congrFun (congrFun h x) y ▸ q).1
/-- PM I ✱71·191. -/
theorem star_71_191 (R : Relation α β) : ManyOne R ↔
    comp (converse R) R = identityOn (codomain R) := by
  constructor
  · intro h; funext x y; apply propext; constructor
    · rintro ⟨z,hzx,hzy⟩; exact ⟨h hzx hzy,⟨z,hzy⟩⟩
    · rintro ⟨rfl,z,hzy⟩; exact ⟨z,hzy,hzy⟩
  · intro h x y z hy hz
    have q : comp (converse R) R y z := ⟨x,hy,hz⟩
    exact (congrFun (congrFun h y) z ▸ q).1
/-- PM I ✱71·192. -/
theorem star_71_192 (R : Relation α β) : OneOne R ↔
    comp R (converse R) = identityOn (domain R) ∧
    comp (converse R) R = identityOn (codomain R) := by rw [OneOne,star_71_19,star_71_191]

end PM.Architecture.Star71UniquenessKernel
