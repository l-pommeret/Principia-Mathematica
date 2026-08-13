import Principia.Architecture.Star25FinalKernel

/-! PM I ✱61, complete extensional relation-subclass calculus (pp. 412–414). -/
namespace PM.Architecture.Star61Kernel
open PM.Architecture.Star25OpeningKernel
open PM.Architecture.Star25MiddleKernel

abbrev RelClass (L : Sort u) (R : Sort v) := Relation L R → Prop
def Rl (p : Relation L R) : RelClass L R := fun r => Included r p
def RlEx (p : Relation L R) : RelClass L R := fun r => Included r p ∧ existsRelation r
def singleton (r : Relation L R) : RelClass L R := fun s => s = r
def classDiff (a b : RelClass L R) : RelClass L R := fun r => a r ∧ ¬ b r
def classUnion (a b : RelClass L R) : RelClass L R := fun r => a r ∨ b r
def ClassIncluded (a b : RelClass L R) := ∀ r, a r → b r
def Sum (a : RelClass L R) : Relation L R := fun x y => ∃ r, a r ∧ r x y
def Product (a : RelClass L R) : Relation L R := fun x y => ∀ r, a r → r x y
def RlImage (a : RelClass L R) : RelClass L R := Rl (Product a)
def PairRelation (x : L) (y : R) : Relation L R := fun a b => a = x ∧ b = y
def pairClass (p q : Relation L R) : RelClass L R := fun r => r = p ∨ r = q
def Rel2 (L : Sort u) (R : Sort v) := Rl (universalRelation (Relation L R) (Relation L R))
def Rel3 (L : Sort u) (R : Sort v) := Rl (universalRelation (Relation (Relation L R) (Relation L R)) (Relation (Relation L R) (Relation L R)))

theorem star_61_01 (l : RelClass L R) (p : Relation L R) : (l = Rl p) = (l = fun r => Included r p) := rfl
theorem star_61_02 (l : RelClass L R) (p : Relation L R) : (l = RlEx p) = (l = fun r => Included r p ∧ existsRelation r) := rfl
theorem star_61_03 : Rel2 L R = Rl (universalRelation (Relation L R) (Relation L R)) := rfl
theorem star_61_04 : Rel3 L R = Rl (universalRelation (Relation (Relation L R) (Relation L R)) (Relation (Relation L R) (Relation L R))) := rfl
theorem star_61_1 (l : RelClass L R) (p : Relation L R) : l = Rl p ↔ l = fun r => Included r p := Iff.rfl
theorem star_61_11 (l : RelClass L R) (p : Relation L R) : l = RlEx p ↔ l = fun r => Included r p ∧ existsRelation r := Iff.rfl
theorem star_61_12 (p : Relation L R) : Rl p = fun r => Included r p := rfl
theorem star_61_13 (p : Relation L R) : RlEx p = fun r => Included r p ∧ existsRelation r := rfl
theorem star_61_14 (p : Relation L R) : ∃ l, l = Rl p := ⟨_, rfl⟩
theorem star_61_15 (p : Relation L R) : ∃ l, l = RlEx p := ⟨_, rfl⟩
theorem star_61_2 (r p : Relation L R) : Rl p r ↔ Included r p := Iff.rfl
theorem star_61_21 (r p : Relation L R) : RlEx p r ↔ Included r p ∧ existsRelation r := Iff.rfl
theorem star_61_22 (r p : Relation L R) : RlEx p r ↔ Rl p r ∧ existsRelation r := Iff.rfl
theorem star_61_23 (r p : Relation L R) : RlEx p r ↔ classDiff (Rl p) (singleton (nullRelation L R)) r := by simp [RlEx,classDiff,singleton,Rl,PM.Architecture.Star25FinalKernel.star_25_54]
theorem star_61_24 (p : Relation L R) : RlEx p = classDiff (Rl p) (singleton (nullRelation L R)) := by funext r; apply propext; exact star_61_23 r p
theorem star_61_3 (p : Relation L R) : Rl p (nullRelation L R) := fun _ _ h => False.elim h
theorem star_61_31 (p : Relation L R) : Rl p (nullRelation L R) := star_61_3 p
theorem star_61_32 : Rl (nullRelation L R) = singleton (nullRelation L R) := by
  funext r; apply propext; constructor
  · intro h; funext x y; apply propext; exact ⟨h x y, fun z => z.elim⟩
  · rintro rfl; exact star_61_3 _
theorem star_61_321 (p : Relation L R) : p = nullRelation L R ↔ Rl p = singleton p := by
  constructor
  · rintro rfl; exact star_61_32
  · intro h; have hn : Rl p (nullRelation L R) := star_61_3 p
    rw [h] at hn; exact hn.symm
theorem star_61_33 : RlEx (nullRelation L R) = fun _ => False := by
  funext r; apply propext; constructor
  · rintro ⟨h,⟨x,y,hr⟩⟩; exact h x y hr
  · intro h; exact h.elim
theorem star_61_34 (p : Relation L R) : Rl p p := fun _ _ h => h
theorem star_61_35 (p : Relation L R) : existsRelation p → RlEx p p := fun h => ⟨star_61_34 p,h⟩
theorem star_61_36 (p : Relation L R) : existsRelation p → ∃ r, RlEx p r := fun h => ⟨p,star_61_35 p h⟩
theorem star_61_361 (p : Relation L R) : existsRelation p ↔ ∃ r, RlEx p r := by
  exact ⟨star_61_36 p, fun ⟨r,h⟩ => PM.Architecture.Star25FinalKernel.star_25_58 r p h.1 h.2⟩
theorem star_61_362 (x : L) (y : R) : Rl (PairRelation x y) = classUnion (singleton (nullRelation L R)) (singleton (PairRelation x y)) := by
  funext r; apply propext; constructor
  · intro h; by_cases e : existsRelation r
    · right; funext a b; apply propext; constructor
      · exact h a b
      · rintro ⟨rfl,rfl⟩; rcases e with ⟨c,d,hcd⟩; have hc := h c d hcd; rcases hc with ⟨rfl,rfl⟩; exact hcd
    · left; exact (PM.Architecture.Star25FinalKernel.star_25_51 r).1 e
  · rintro (rfl|rfl); exact star_61_3 _; exact star_61_34 _
theorem star_61_37 (x : L) (y : R) : RlEx (PairRelation x y) = singleton (PairRelation x y) := by
  funext r; apply propext; constructor
  · rintro ⟨hr, ⟨a,b,hab⟩⟩
    funext c d; apply propext; constructor
    · exact hr c d
    · rintro ⟨rfl,rfl⟩
      rcases hr a b hab with ⟨rfl,rfl⟩; exact hab
  · intro e; subst r; exact ⟨star_61_34 _,⟨x,y,⟨rfl,rfl⟩⟩⟩
theorem star_61_371 (r : Relation L R) (h : ∃ x y, r = PairRelation x y) : Rl r = classUnion (singleton (nullRelation L R)) (singleton r) := by rcases h with ⟨x,y,rfl⟩; exact star_61_362 x y
theorem star_61_372 (r : Relation L R) (h : ∃ x y, r = PairRelation x y) : ClassIncluded (Rl r) (classUnion (singleton (nullRelation L R)) (fun s => ∃ a b, s = PairRelation a b)) := by
  rcases h with ⟨x,y,rfl⟩; rw [star_61_362]; intro s hs; exact hs.elim Or.inl (fun e => Or.inr ⟨x,y,e⟩)
theorem star_61_373 (r : Relation L R) (h : ∃ x y, r = PairRelation x y) : ClassIncluded (Rl r) (classUnion (singleton (nullRelation L R)) (fun s => ∃ a b, s = PairRelation a b)) := star_61_372 r h
theorem star_61_38 (r : Relation L R) : (∃ x y, r = PairRelation x y) → RlEx r = singleton r := by rintro ⟨x,y,rfl⟩; exact star_61_37 x y
theorem star_61_39 (x z : L) (y w : R) : Rl (union (PairRelation x y) (PairRelation z w)) = classUnion (classUnion (classUnion (singleton (nullRelation L R)) (singleton (PairRelation x y))) (singleton (PairRelation z w))) (singleton (union (PairRelation x y) (PairRelation z w))) := by
  funext r; apply propext; constructor
  · intro h; classical
    by_cases hx : r x y
    · by_cases hz : r z w
      · right; funext a b; apply propext; constructor
        · exact h a b
        · rintro (e|e)
          · rcases e with ⟨rfl,rfl⟩; exact hx
          · rcases e with ⟨rfl,rfl⟩; exact hz
      · left; left; right; funext a b; apply propext; constructor
        · intro hr; rcases h a b hr with ha|hb
          · exact ha
          · rcases hb with ⟨rfl,rfl⟩; exact (hz hr).elim
        · intro ha; rcases ha with ⟨rfl,rfl⟩; exact hx
    · by_cases hz : r z w
      · left; right; funext a b; apply propext; constructor
        · intro hr; rcases h a b hr with ha|hb
          · rcases ha with ⟨rfl,rfl⟩; exact (hx hr).elim
          · exact hb
        · intro hb; rcases hb with ⟨rfl,rfl⟩; exact hz
      · left; left; left; funext a b; apply propext; constructor
        · intro hr; rcases h a b hr with ha|hb
          · rcases ha with ⟨rfl,rfl⟩; exact (hx hr).elim
          · rcases hb with ⟨rfl,rfl⟩; exact (hz hr).elim
        · intro hf; exact hf.elim
  · rintro (((rfl|rfl)|rfl)|rfl)
    · exact star_61_3 _
    · intro a b h; exact Or.inl h
    · intro a b h; exact Or.inr h
    · exact star_61_34 _
theorem star_61_391 (p q : Relation L R) (hp:∃ x y,p=PairRelation x y) (hq:∃ x y,q=PairRelation x y) : Rl (union p q)=classUnion (classUnion (classUnion (singleton (nullRelation L R)) (singleton p)) (singleton q)) (singleton (union p q)) := by rcases hp with ⟨x,y,rfl⟩; rcases hq with ⟨z,w,rfl⟩; exact star_61_39 x z y w
theorem star_61_4 (q p r : Relation L R) : Rl p q → Included r q → Rl p r := fun hq hr x y h => hq x y (hr x y h)
theorem star_61_41 (q p r : Relation L R) : Rl p q → Rl p (intersection q r) := fun h x y z => h x y z.1
theorem star_61_42 (q p r : Relation L R) : Rl p q → Included r q → existsRelation r → RlEx p r := fun hq hr he => ⟨star_61_4 q p r hq hr,he⟩
theorem star_61_43 (q r p : Relation L R) : (Rl p q ∧ Rl p r) ↔ Rl p (union q r) := by exact ⟨fun h x y z => z.elim (h.1 x y) (h.2 x y), fun h => ⟨fun x y z=>h x y (Or.inl z),fun x y z=>h x y (Or.inr z)⟩⟩
theorem star_61_44 (q r p : Relation L R) : Rl p q → RlEx p r → RlEx p (union q r) := fun hq hr => ⟨(star_61_43 q r p).1 ⟨hq,hr.1⟩,(PM.Architecture.Star25FinalKernel.star_25_56 q r).2 (Or.inr hr.2)⟩
theorem star_61_5 (p : Relation L R) : Sum (Rl p)=p := by funext x y; apply propext; exact ⟨fun ⟨r,h,hr⟩=>h x y hr,fun hp=>⟨p,star_61_34 p,hp⟩⟩
theorem star_61_501 (p : Relation L R) : Sum (RlEx p)=p := by funext x y; apply propext; exact ⟨fun ⟨r,h,hr⟩=>h.1 x y hr,fun hp=>⟨PairRelation x y,⟨fun a b h=>by rcases h with ⟨rfl,rfl⟩;exact hp,⟨x,y,rfl,rfl⟩⟩,rfl,rfl⟩⟩
theorem star_61_51 (p : Relation L R) : Product (Rl p)=nullRelation L R := by funext x y; apply propext; exact ⟨fun h=>h _ (star_61_3 p),fun z=>z.elim⟩
theorem star_61_52 (l : RelClass L R) (q : Relation L R) : Included (Sum l) q ↔ ClassIncluded l (Rl q) := by exact ⟨fun h r hr x y hx=>h x y ⟨r,hr,hx⟩,fun h x y ⟨r,hr,hx⟩=>h r hr x y hx⟩
theorem star_61_53 (q : Relation L R) (l : RelClass L R) : Included q (Product l) ↔ ∀ r, l r → Included q r := by
  constructor <;> intro h
  · intro r hr x y hq; exact h x y hq r hr
  · intro x y hq r hr; exact h r hr x y hq
theorem star_61_54 (l : RelClass L R) : Rl (Product l)=RlImage l := rfl
theorem star_61_55 (p q : Relation L R) : Rl p=Rl q ↔ p=q := by
  constructor
  · intro h; funext x y; apply propext; constructor
    · intro hp; have z : Rl q p := (congrFun h p) ▸ star_61_34 p; exact z x y hp
    · intro hq; have z : Rl p q := (congrFun h q).symm ▸ star_61_34 q; exact z x y hq
  · rintro rfl; rfl
theorem star_61_56 (p q : Relation L R) : RlEx p=RlEx q ↔ p=q := by constructor; intro h; funext x y; apply propext; constructor; intro hp; have a:RlEx p (PairRelation x y):=⟨fun a b z=>by rcases z with ⟨rfl,rfl⟩;exact hp,⟨x,y,rfl,rfl⟩⟩; rw [h] at a; exact a.1 x y ⟨rfl,rfl⟩; intro hq; have a:RlEx q (PairRelation x y):=⟨fun a b z=>by rcases z with ⟨rfl,rfl⟩;exact hq,⟨x,y,rfl,rfl⟩⟩; rw [←h] at a; exact a.1 x y ⟨rfl,rfl⟩; intro e;subst q;rfl
theorem star_61_6 (p : Relation L R) (x:L)(y:R) : p x y → RlEx p (PairRelation x y) := fun h=>⟨fun a b z=>by rcases z with ⟨rfl,rfl⟩;exact h,⟨x,y,rfl,rfl⟩⟩
theorem star_61_62 (p : Relation L R) (x z:L)(y w:R) : p x y → p z w → RlEx p (union (PairRelation x y) (PairRelation z w)) := fun h1 h2=>⟨fun a b h=>h.elim (fun z=>by rcases z with ⟨rfl,rfl⟩;exact h1) (fun z=>by rcases z with ⟨rfl,rfl⟩;exact h2),⟨x,y,Or.inl ⟨rfl,rfl⟩⟩⟩
theorem star_61_7 (p : Relation L R) : ∃ l : RelClass L R, l=Rl p := ⟨_,rfl⟩
end PM.Architecture.Star61Kernel
