import Principia.Architecture.Star88OpeningKernel

namespace PM.Architecture.Star88SecondKernel

open Star88OpeningKernel

def Empty : Class α := fun _ => False
def AvoidsEmpty (k : Class (Class α)) := ¬ k Empty
def NonemptyFamily (k : Class (Class α)) := ∀ a, k a → NonemptyClass a
def Subfamily (q k : Class (Class α)) := Included q k
def ProperClasses : Class (Class α) := fun a => NonemptyClass a
def ClassOfSubfamilies (k : Class (Class α)) : Class (Class (Class α)) :=
  fun q => Subfamily q k

theorem nonemptyFamily_iff_avoidsEmpty (k : Class (Class α)) :
    NonemptyFamily k ↔ AvoidsEmpty k := by
  classical
  constructor
  · intro h hk; obtain ⟨x, hx⟩ := h Empty hk; exact hx
  · intro h a ha
    exact Classical.byContradiction fun hn => by
      apply h
      have hae : a = Empty := by
        funext x; apply propext; constructor
        · intro hx; exact (hn ⟨x, hx⟩).elim
        · intro hx; exact hx.elim
      simpa [hae] using ha

theorem star_88_37 (hax : MultiplicativeAxiom α) (k : Class (Class α)) :
    AvoidsEmpty k → DisjointFamily k → Multipliable k := by
  intro hne hd
  exact hax k ((nonemptyFamily_iff_avoidsEmpty k).2 hne) hd

theorem star_88_371 (hax : MultiplicativeAxiom α) (k : Class (Class α))
    (hd : DisjointFamily k) : AvoidsEmpty k ↔ Multipliable k := by
  constructor
  · intro h; exact star_88_37 hax k h hd
  · rintro ⟨μ, hμ⟩ hk
    obtain ⟨x, _, hx, _⟩ := hμ Empty hk
    exact hx

theorem star_88_372 (hax : MultiplicativeAxiom α) (k : Class (Class α))
    (hd : DisjointFamily k) : k Empty ↔ ¬ Multipliable k := by
  constructor
  · intro hk hm
    obtain ⟨μ, hμ⟩ := hm
    obtain ⟨x, _, hx, _⟩ := hμ Empty hk
    exact hx
  · intro hnm
    exact Classical.byContradiction fun hne =>
      hnm ((star_88_371 hax k hd).1 hne)

theorem star_88_373 (hax : MultiplicativeAxiom α) (k : Class (Class α))
    (hne : NonemptyFamily k) (hd : DisjointFamily k) :
    ∀ q, ClassOfSubfamilies k q → Multipliable q := by
  intro q hq
  exact star_88_11 k q (hax k hne hd) hq

theorem star_88_38 (hax : MultiplicativeAxiom α) (k : Class (Class α))
    (hne : NonemptyFamily k) (hd : DisjointFamily k) : Multipliable k := hax k hne hd

theorem star_88_39 (hax : MultiplicativeAxiom α) :
    ∀ k : Class (Class α), NonemptyFamily k → DisjointFamily k → ∃ μ, Selector k μ := hax

theorem star_88_4 (k : Class (Class α)) (q : Class (Class α))
    (hq : Subfamily q k) : Subfamily q k := hq

theorem star_88_41 (k : Class (Class α)) (hk : Multipliable k) :
    ∃ μ, Selector k μ := hk

theorem star_88_411 (k : Class (Class α)) (hk : Multipliable k) :
    Multipliable k := hk

theorem star_88_42 (k : Class (Class α)) : Multipliable k ↔ ∃ μ, Selector k μ := Iff.rfl

theorem star_88_43 (k q : Class (Class α)) :
    Multipliable k → Subfamily q k → Multipliable q := star_88_11 k q

theorem star_88_431 (k q : Class (Class α)) (hq : Subfamily q k) :
    Multipliable k → Multipliable q := fun hk => star_88_11 k q hk hq

theorem star_88_44 (k q : Class (Class α)) :
    Multipliable k → Subfamily q k → Multipliable q := star_88_11 k q

theorem star_88_441 (k q : Class (Class α)) (hq : Subfamily q k)
    (hk : Multipliable k) : Multipliable q := star_88_11 k q hk hq

theorem star_88_45 (P : Class (Class α)) (hP : Multipliable P) : Multipliable P := hP

end PM.Architecture.Star88SecondKernel
