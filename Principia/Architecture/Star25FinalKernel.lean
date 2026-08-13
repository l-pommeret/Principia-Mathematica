import Principia.Architecture.Star25DecompositionKernel

/-! Remaining PM I propositions ✱25·492–✱25·63 (pp. 244–245). -/
namespace PM.Architecture.Star25FinalKernel
open PM.Architecture.Star25OpeningKernel
open PM.Architecture.Star25MiddleKernel

abbrev RelationExists (r : Relation Left Right) : Prop := existsRelation r

theorem star_25_492 (p q r : Relation Left Right) :
    Included q p → difference p q = r → difference p r = q := by
  intro hqp hpr; funext x y; apply propext; constructor
  · rintro ⟨hp, hnr⟩; by_cases hq : q x y
    · exact hq
    · have : r x y := by rw [← hpr]; exact ⟨hp, hq⟩
      exact False.elim (hnr this)
  · intro hq; refine ⟨hqp x y hq, ?_⟩
    intro hr; have hd : difference p q x y := by rw [hpr]; exact hr
    exact hd.2 hq

theorem star_25_493 (p q r : Relation Left Right) :
    intersection q r = nullRelation Left Right →
      p = union (difference p q) (difference p r) := by
  intro hd; funext x y; apply propext; constructor
  · intro hp; by_cases hq : q x y
    · right; refine ⟨hp, ?_⟩; intro hr
      have z : nullRelation Left Right x y := by rw [← hd]; exact ⟨hq,hr⟩
      exact z
    · exact Or.inl ⟨hp,hq⟩
  · rintro (⟨hp,_⟩|⟨hp,_⟩) <;> exact hp

theorem star_25_494 (p q r s : Relation Left Right) :
    Included r p → Included s q → intersection p q = nullRelation Left Right →
      difference (union r s) p = s ∧ difference (union r s) q = r := by
  intro hr hs hd; constructor
  · funext x y; apply propext; constructor
    · rintro ⟨hrx|hsx,hnp⟩
      · exact False.elim (hnp (hr x y hrx))
      · exact hsx
    · intro hsx; refine ⟨Or.inr hsx, ?_⟩; intro hp
      have z : nullRelation Left Right x y := by rw [← hd]; exact ⟨hp,hs x y hsx⟩
      exact z
  · funext x y; apply propext; constructor
    · rintro ⟨hrx|hsx,hnq⟩
      · exact hrx
      · exact False.elim (hnq (hs x y hsx))
    · intro hrx; refine ⟨Or.inl hrx, ?_⟩; intro hq
      have z : nullRelation Left Right x y := by rw [← hd]; exact ⟨hr x y hrx,hq⟩
      exact z

theorem star_25_495 (p q r : Relation Left Right) :
    intersection p r = nullRelation Left Right →
      difference (union p r) (union q r) = difference p q := by
  intro hd; funext x y; apply propext; constructor
  · rintro ⟨hp|hr,hnot⟩
    · exact ⟨hp, fun hq => hnot (Or.inl hq)⟩
    · exact False.elim (hnot (Or.inr hr))
  · rintro ⟨hp,hnq⟩; refine ⟨Or.inl hp, ?_⟩
    rintro (hq|hr)
    · exact hnq hq
    · have z : nullRelation Left Right x y := by rw [← hd]; exact ⟨hp,hr⟩
      exact z

theorem star_25_5 (r : Relation Left Right) : RelationExists r ↔ ∃ x y, r x y := Iff.rfl

theorem star_25_51 (r : Relation Left Right) :
    ¬ RelationExists r ↔ r = nullRelation Left Right := by
  constructor
  · intro hn; funext x y; apply propext
    exact ⟨fun h => False.elim (hn ⟨x,y,h⟩), fun z => False.elim z⟩
  · rintro rfl ⟨x,y,h⟩; exact h

theorem star_25_52 [Nonempty Left] [Nonempty Right] :
    RelationExists (universalRelation Left Right) :=
  ⟨Classical.choice inferInstance, Classical.choice inferInstance, True.intro⟩

theorem star_25_53 : ¬ RelationExists (nullRelation Left Right) := by
  rintro ⟨x,y,h⟩; exact h

theorem star_25_54 (r : Relation Left Right) :
    RelationExists r ↔ r ≠ nullRelation Left Right := by
  constructor
  · rintro ⟨x,y,h⟩ eq; rw [eq] at h; exact h
  · intro ne; apply Classical.byContradiction; intro hn
    exact ne ((star_25_51 r).1 hn)

theorem star_25_55 (r s : Relation Left Right) :
    ¬ Included r s ↔ RelationExists (difference r s) := by
  constructor
  · intro hn; apply Classical.byContradiction; intro he
    apply hn; intro x y hr; apply Classical.byContradiction; intro hs
    exact he ⟨x,y,⟨hr,hs⟩⟩
  · rintro ⟨x,y,⟨hr,hns⟩⟩ included; exact hns (included x y hr)

theorem star_25_56 (r s : Relation Left Right) :
    RelationExists (union r s) ↔ RelationExists r ∨ RelationExists s := by
  constructor
  · rintro ⟨x,y,hr|hs⟩
    · exact Or.inl ⟨x,y,hr⟩
    · exact Or.inr ⟨x,y,hs⟩
  · rintro (⟨x,y,hr⟩|⟨x,y,hs⟩)
    · exact ⟨x,y,Or.inl hr⟩
    · exact ⟨x,y,Or.inr hs⟩

theorem star_25_561 (r s : Relation Left Right) :
    RelationExists (intersection r s) → RelationExists r ∧ RelationExists s := by
  rintro ⟨x,y,hr,hs⟩; exact ⟨⟨x,y,hr⟩,⟨x,y,hs⟩⟩

theorem star_25_57 (r s : Relation Left Right) :
    intersection r s = nullRelation Left Right → RelationExists r → r ≠ s := by
  rintro hd ⟨x,y,hr⟩ eq; subst s
  have z : nullRelation Left Right x y := by rw [← hd]; exact ⟨hr,hr⟩
  exact z

theorem star_25_571 (r s : Relation Left Right) :
    RelationExists r → r = s → RelationExists (intersection r s) := by
  rintro ⟨x,y,hr⟩ rfl; exact ⟨x,y,hr,hr⟩

theorem star_25_58 (r s : Relation Left Right) :
    Included r s → RelationExists r → RelationExists s := by
  rintro h ⟨x,y,hr⟩; exact ⟨x,y,h x y hr⟩

theorem star_25_6 (r s : Relation Left Right) :
    Included r s → (r ≠ s ↔ RelationExists (difference s r)) := by
  intro hrs; constructor
  · intro ne; apply Classical.byContradiction; intro hn
    have empty := (star_25_51 (difference s r)).1 hn
    apply ne; funext x y; apply propext; constructor
    · exact hrs x y
    · intro hs; apply Classical.byContradiction; intro hnr
      have z : nullRelation Left Right x y := by rw [← empty]; exact ⟨hs,hnr⟩
      exact z
  · rintro ⟨x,y,hs,hnr⟩ eq; exact hnr (by rw [eq]; exact hs)

theorem star_25_61 (r s : Relation Left Right) :
    ¬ RelationExists s → union r s = r := by
  intro hn; funext x y; apply propext; constructor
  · rintro (hr|hs); exact hr; exact False.elim (hn ⟨x,y,hs⟩)
  · exact Or.inl

theorem star_25_62 (r s : Relation Left Right) :
    ¬ RelationExists s → intersection r s = nullRelation Left Right := by
  intro hn; funext x y; apply propext
  exact ⟨fun h => False.elim (hn ⟨x,y,h.2⟩), fun z => False.elim z⟩

theorem star_25_63 (kappa : Relation Left Right → Prop) :
    ¬ kappa (nullRelation Left Right) ↔
      ∀ r, kappa r → RelationExists r := by
  constructor
  · intro hnull r hr; apply Classical.byContradiction; intro hn
    have eq := (star_25_51 r).1 hn; exact hnull (eq ▸ hr)
  · intro all hnull; exact star_25_53 (all _ hnull)

end PM.Architecture.Star25FinalKernel
