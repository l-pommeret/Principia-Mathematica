/-! # PM I, ✱73: relational infrastructure for similarity of classes. -/

namespace PM.Architecture.Star73Prerequisites

abbrev Class (A : Sort u) := A → Prop
abbrev Relation (A : Sort u) (B : Sort v) := A → B → Prop

def Included (a b : Class A) := ∀ ⦃x⦄, a x → b x
def Domain (R : Relation A B) : Class A := fun x => ∃ y, R x y
def ConverseDomain (R : Relation A B) : Class B := fun y => ∃ x, R x y
def RestrictDomain (a : Class A) (R : Relation A B) : Relation A B :=
  fun x y => a x ∧ R x y
def RestrictRange (R : Relation A B) (b : Class B) : Relation A B :=
  fun x y => R x y ∧ b y
def Image (R : Relation A B) (a : Class A) : Class B :=
  fun y => ∃ x, a x ∧ R x y
def Preimage (R : Relation A B) (b : Class B) : Class A :=
  fun x => ∃ y, b y ∧ R x y
def Converse (R : Relation A B) : Relation B A := fun y x => R x y
def Compose (R : Relation A B) (S : Relation B C) : Relation A C :=
  fun x z => ∃ y, R x y ∧ S y z

def Functional (R : Relation A B) := ∀ ⦃x y z⦄, R x y → R x z → y = z
def Injective (R : Relation A B) := ∀ ⦃x y z⦄, R x z → R y z → x = y
def OneOne (R : Relation A B) := Functional R ∧ Injective R
def Similar (a : Class A) (b : Class B) :=
  ∃ R : Relation A B, OneOne R ∧ Domain R = a ∧ ConverseDomain R = b

theorem image_eq_converseDomain_restrict (R : Relation A B) (a : Class A) :
    Image R a = ConverseDomain (RestrictDomain a R) := rfl

theorem preimage_eq_domain_restrict (R : Relation A B) (b : Class B) :
    Preimage R b = Domain (RestrictRange R b) := by
  funext x
  apply propext
  exact ⟨fun ⟨y, hy, hR⟩ => ⟨y, hR, hy⟩,
    fun ⟨y, hR, hy⟩ => ⟨y, hy, hR⟩⟩

theorem oneOne_converse {R : Relation A B} : OneOne (Converse R) ↔ OneOne R := by
  constructor
  · rintro ⟨hf, hi⟩
    constructor
    · intro x y z hxy hxz; exact hi hxy hxz
    · intro x y z hxz hyz; exact hf hxz hyz
  · rintro ⟨hf, hi⟩
    constructor
    · intro x y z hxy hxz; exact hi hxy hxz
    · intro x y z hxz hyz; exact hf hxz hyz

theorem oneOne_restrictDomain {R : Relation A B} (h : OneOne R) (a : Class A) :
    OneOne (RestrictDomain a R) := by
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨_, hxy⟩ ⟨_, hxz⟩; exact h.1 hxy hxz
  · rintro x y z ⟨_, hxz⟩ ⟨_, hyz⟩; exact h.2 hxz hyz

theorem oneOne_restrictRange {R : Relation A B} (h : OneOne R) (b : Class B) :
    OneOne (RestrictRange R b) := by
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨hxy, _⟩ ⟨hxz, _⟩; exact h.1 hxy hxz
  · rintro x y z ⟨hxz, _⟩ ⟨hyz, _⟩; exact h.2 hxz hyz

theorem oneOne_compose {R : Relation A B} {S : Relation B C}
    (hR : OneOne R) (hS : OneOne S) : OneOne (Compose R S) := by
  refine ⟨?_, ?_⟩
  · rintro x z w ⟨y, hxy, hyz⟩ ⟨y', hxy', hy'w⟩
    have : y = y' := hR.1 hxy hxy'
    subst y'; exact hS.1 hyz hy'w
  · rintro x y z ⟨u, hxu, huz⟩ ⟨v, hyv, hvz⟩
    have : u = v := hS.2 huz hvz
    subst v; exact hR.2 hxu hyv

end PM.Architecture.Star73Prerequisites
