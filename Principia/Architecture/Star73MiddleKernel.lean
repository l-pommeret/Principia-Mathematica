import Principia.Architecture.Star73OpeningKernel

/-! # PM I, ✱73·26–✱73·46: structural laws of similarity. -/

namespace PM.Architecture.Star73MiddleKernel
open PM.Architecture.Star73Prerequisites

def SingletonClass (x : A) : Class A := fun y => y = x
def SingletonLift (a : Class A) : Class (Class A) := fun p => ∃ x, a x ∧ p = SingletonClass x
def UnitClass (p : Class A) := ∃ x, p = SingletonClass x
def Flatten (s : Class (Class A)) : Class A := fun x => ∃ p, s p ∧ p x
def UniqueMember (a : Class A) := ∃ x, a x ∧ ∀ y, a y → y = x

private theorem similar_refl (a : Class A) : Similar a a := by
  let R : Relation A A := fun x y => a x ∧ y = x
  refine ⟨R, ?_, ?_, ?_⟩
  · constructor
    · rintro x y z ⟨_, rfl⟩ ⟨_, hz⟩; exact hz.symm
    · rintro x y z ⟨_, rfl⟩ ⟨_, hz⟩; exact hz
  · funext x; apply propext
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨x, hx, rfl⟩⟩
  · funext y; apply propext
    exact ⟨fun ⟨x, hx, h⟩ => h ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩

private theorem similar_symm {a : Class A} {b : Class B} : Similar a b → Similar b a := by
  rintro ⟨R, hR, hD, hC⟩
  exact ⟨Converse R, (oneOne_converse).2 hR, hC, hD⟩

private theorem similar_trans {a : Class A} {b : Class B} {c : Class C} :
    Similar a b → Similar b c → Similar a c := by
  rintro ⟨R, hR, hDR, hCR⟩ ⟨S, hS, hDS, hCS⟩
  refine ⟨Compose R S, oneOne_compose hR hS, ?_, ?_⟩
  · funext x; apply propext
    constructor
    · rintro ⟨z, y, hxy, hyz⟩; rw [← hDR]; exact ⟨y, hxy⟩
    · intro hx
      obtain ⟨y, hxy⟩ : Domain R x := by rw [hDR]; exact hx
      have hy : b y := by rw [← hCR]; exact ⟨x, hxy⟩
      obtain ⟨z, hyz⟩ : Domain S y := by rw [hDS]; exact hy
      exact ⟨z, y, hxy, hyz⟩
  · funext z; apply propext
    constructor
    · rintro ⟨x, y, hxy, hyz⟩; rw [← hCS]; exact ⟨y, hyz⟩
    · intro hz
      obtain ⟨y, hyz⟩ : ConverseDomain S z := by rw [hCS]; exact hz
      have hy : b y := by rw [← hDS]; exact ⟨z, hyz⟩
      obtain ⟨x, hxy⟩ : ConverseDomain R y := by rw [hCR]; exact hy
      exact ⟨x, y, hxy, hyz⟩

/-- ✱73·26, a one-one assignment has image similar to its argument class. -/
theorem star_73_26 {R : Relation A B} (hR : OneOne R) (a : Class A)
    (ha : Included a (Domain R)) : Similar (Image R a) a :=
  PM.Architecture.Star73OpeningKernel.star_73_21 hR a ha

/-- ✱73·27, equality of assigned values entails similarity with the image. -/
theorem star_73_27 {R : Relation A B} (hfun : Functional R) (hinj : Injective R)
    (a : Class A) (ha : Included a (Domain R)) : Similar (Image R a) a :=
  star_73_26 ⟨hfun, hinj⟩ a ha

/-- ✱73·28, the explicitly quantified injectivity form. -/
theorem star_73_28 {R : Relation A B}
    (hfun : ∀ ⦃x y z⦄, R x y → R x z → y = z)
    (hinj : ∀ ⦃x y z⦄, R x z → R y z → x = y)
    (a : Class A) (ha : Included a (Domain R)) : Similar (Image R a) a :=
  star_73_27 hfun hinj a ha

/-- ✱73·3, reflexivity of similarity. -/
theorem star_73_3 (a : Class A) : Similar a a := similar_refl a

/-- ✱73·301, conversing a witnessing relation reverses its endpoints. -/
theorem star_73_301 {R : Relation A B} {a : Class A} {b : Class B}
    (hR : OneOne R) (hD : Domain R = a) (hC : ConverseDomain R = b) :
    OneOne (Converse R) ∧ Domain (Converse R) = b ∧ ConverseDomain (Converse R) = a :=
  ⟨(oneOne_converse).2 hR, hC, hD⟩

/-- ✱73·31, symmetry of similarity. -/
theorem star_73_31 (a : Class A) (b : Class B) : Similar a b ↔ Similar b a :=
  ⟨similar_symm, similar_symm⟩

/-- ✱73·311, composition of correlations witnesses the transitive step. -/
theorem star_73_311 {a : Class A} {b : Class B} {c : Class C} :
    Similar a b → Similar b c → Similar a c := similar_trans

/-- ✱73·32, transitivity of similarity. -/
theorem star_73_32 {a : Class A} {b : Class B} {c : Class C} :
    Similar a b → Similar b c → Similar a c := similar_trans

/-- ✱73·33, the converse of the similarity relation is similarity. -/
theorem star_73_33 (a : Class A) (b : Class B) : Similar a b ↔ Similar b a :=
  star_73_31 a b

/-- ✱73·34, similarity is an equivalence relation. -/
theorem star_73_34 : Equivalence (@Similar A A) :=
  ⟨similar_refl, fun {_ _} => similar_symm, fun {_ _ _} => similar_trans⟩

/-- ✱73·35, both arguments of a similarity are classes of their stated types. -/
theorem star_73_35 {a : Class A} {b : Class B} (_ : Similar a b) :
    (∀ x, a x ↔ a x) ∧ (∀ y, b y ↔ b y) := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- ✱73·36, similarity transports unique existence. -/
theorem star_73_36 {a : Class A} {b : Class B} (h : Similar a b) :
    UniqueMember a ↔ UniqueMember b := by
  rcases h with ⟨R, hR, hD, hC⟩
  constructor
  · rintro ⟨x, hx, huniq⟩
    obtain ⟨y, hxy⟩ : Domain R x := by rw [hD]; exact hx
    refine ⟨y, ?_, ?_⟩
    · rw [← hC]; exact ⟨x, hxy⟩
    · intro z hz
      obtain ⟨w, hwz⟩ : ConverseDomain R z := by rw [hC]; exact hz
      have hw : a w := by rw [← hD]; exact ⟨z, hwz⟩
      have hwx := huniq w hw
      subst w; exact (hR.1 hxy hwz).symm
  · rintro ⟨y, hy, huniq⟩
    obtain ⟨x, hxy⟩ : ConverseDomain R y := by rw [hC]; exact hy
    refine ⟨x, ?_, ?_⟩
    · rw [← hD]; exact ⟨y, hxy⟩
    · intro z hz
      obtain ⟨w, hzw⟩ : Domain R z := by rw [hD]; exact hz
      have hw : b w := by rw [← hC]; exact ⟨z, hzw⟩
      have hwy := huniq w hw
      subst w; exact hR.2 hzw hxy

/-- ✱73·37, cancellation through a common similar class. -/
theorem star_73_37 {a : Class A} {b : Class B} {c : Class C}
    (hab : Similar a b) : Similar c a ↔ Similar c b := by
  constructor
  · intro hca; exact similar_trans hca hab
  · intro hcb; exact similar_trans hcb (similar_symm hab)

/-- ✱73·4, conversing every member of a relational class preserves similarity. -/
theorem star_73_4 (s : Class (Relation A B)) :
    Similar (fun R : Relation B A => ∃ Q, s Q ∧ R = Converse Q) s := by
  let C : Relation (Relation B A) (Relation A B) := fun R Q => s Q ∧ R = Converse Q
  refine ⟨C, ?_, ?_, ?_⟩
  · constructor <;> rintro _ _ _ ⟨_, rfl⟩ ⟨_, h⟩
    · have hh := congrArg Converse h
      simpa [Converse] using hh
    · exact h.symm
  · funext R; apply propext
    exact ⟨fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, h⟩,
      fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, h⟩⟩
  · funext Q; apply propext
    exact ⟨fun ⟨_, hQ, _⟩ => hQ, fun hQ => ⟨Converse Q, hQ, rfl⟩⟩

/-- ✱73·41, the class of singleton representatives is similar to the class. -/
theorem star_73_41 (a : Class A) : Similar (SingletonLift a) a := by
  let R : Relation (Class A) A := fun p x => a x ∧ p = SingletonClass x
  refine ⟨R, ?_, ?_, ?_⟩
  · constructor
    · rintro p x y ⟨_, hp⟩ ⟨_, hq⟩
      have := congrFun (hp.symm.trans hq) x
      simpa [SingletonClass] using this.mp rfl
    · rintro p q x ⟨_, hp⟩ ⟨_, hq⟩; exact hp.trans hq.symm
  · rfl
  · funext x; apply propext
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨SingletonClass x, hx, rfl⟩⟩

/-- ✱73·42, flattening a class of pairwise distinct unit classes preserves size. -/
theorem star_73_42 (a : Class A) : Similar (Flatten (SingletonLift a)) a := by
  have hf : Flatten (SingletonLift a) = a := by
    funext x; apply propext
    exact ⟨fun ⟨p, ⟨y, hy, hpy⟩, hp⟩ => by
        rw [hpy] at hp
        simpa [SingletonClass] using hp ▸ hy,
      fun hx => ⟨SingletonClass x, ⟨x, hx, rfl⟩, rfl⟩⟩
  rw [hf]; exact similar_refl a

/-- ✱73·43, singleton lifting respects similarity. -/
theorem star_73_43 {a : Class A} {b : Class B} (h : Similar a b) :
    Similar (SingletonLift a) (SingletonLift b) :=
  similar_trans (star_73_41 a) (similar_trans h (similar_symm (star_73_41 b)))

/-- ✱73·44, a class similar to a singleton is itself a unit class. -/
theorem star_73_44 {b : Class B} (x : A) (h : Similar (SingletonClass x) b) :
    UniqueMember b := (star_73_36 h).mp ⟨x, rfl, fun _ hy => hy⟩

/-- ✱73·45, similarity to a singleton is equivalent to unique membership. -/
theorem star_73_45 (x : A) (b : Class B) :
    Similar (SingletonClass x) b ↔ UniqueMember b := by
  constructor
  · exact star_73_44 x
  · rintro ⟨y, hy, hu⟩
    let R : Relation A B := fun u v => u = x ∧ v = y
    refine ⟨R, ?_, ?_, ?_⟩
    · exact ⟨by rintro _ _ _ ⟨_, rfl⟩ ⟨_, rfl⟩; rfl,
        by rintro _ _ _ ⟨rfl, _⟩ ⟨rfl, _⟩; rfl⟩
    · funext u; apply propext; simp [Domain, R, SingletonClass]
    · funext v; apply propext
      constructor
      · rintro ⟨_, _, rfl⟩; exact hy
      · intro hv; exact ⟨x, rfl, hu v hv⟩

/-- ✱73·46, similarity is inhabited as a relation (by reflexivity). -/
theorem star_73_46 (a : Class A) : ∃ b : Class A, Similar a b := ⟨a, similar_refl a⟩

end PM.Architecture.Star73MiddleKernel
