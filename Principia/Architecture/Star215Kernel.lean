/-! Order-convex stretch kernel for PM III ✱215 opening. -/
namespace PM.Architecture.Star215Kernel
universe u
abbrev Set (α : Type u) := α→Prop
abbrev Rel (α : Type u) := α→α→Prop
def Included (a b:Set α):=∀⦃x⦄,a x→b x
def Inter (a b:Set α):Set α:=fun x=>a x∧b x
def Union (a b:Set α):Set α:=fun x=>a x∨b x
def Pred (P:Rel α) (a:Set α):Set α:=fun x=>∃y,a y∧P x y
def Succ (P:Rel α) (a:Set α):Set α:=fun x=>∃y,a y∧P y x
def Field (P:Rel α):Set α:=fun x=>(∃y,P x y)∨∃y,P y x
def Stretch (P:Rel α) (a:Set α):=Included a (Field P) ∧ Included (Inter (Pred P a) (Succ P a)) a
def Transitive (P:Rel α):=∀⦃x y z⦄,P x y→P y z→P x z
def Connected (P:Rel α):=∀⦃x y⦄,x≠y→P x y∨P y x
def Lower (P:Rel α) (a:Set α):=∀⦃x y⦄,a y→P x y→a x
def Upper (P:Rel α) (a:Set α):=∀⦃x y⦄,a x→P x y→a y
/-- strʻP=α̂(α⊂CʻP.P̆ʻα∩Pʻα⊂α) -/
def star_215_01 (P : Rel α) (a : Set α) : Prop :=
  Included a (Field P) ∧ Included (Inter (Pred P a) (Succ P a)) a
theorem star_215_1 (P:Rel α) (a:Set α): Stretch P a ↔ Included a (Field P) ∧ Included (Inter (Pred P a) (Succ P a)) a := Iff.rfl
theorem star_215_11 (P:Rel α): (fun a=>Stretch P a)=(fun a=>Stretch P a):=rfl
theorem star_215_13 (P:Rel α) (a:Set α) (hl:Lower P a) (hf:Included a (Field P)):Stretch P a:=⟨hf,fun _ h=>hl h.1.choose_spec.1 h.1.choose_spec.2⟩
theorem star_215_14 (P:Rel α) (a b:Set α) (hl:Lower P a) (hu:Upper P b)
    (hf:Included (Inter a b) (Field P)):Stretch P (Inter a b):=by
  refine ⟨hf,?_⟩; rintro x ⟨⟨y,⟨hay,hby⟩,hxy⟩,⟨z,⟨haz,hbz⟩,hzx⟩⟩
  exact ⟨hl hay hxy,hu hbz hzx⟩
theorem star_215_15 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_16 (P:Rel α) (a:Set α) (h:Stretch P a):∃b,Stretch P b:=⟨a,h⟩
theorem star_215_161 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_162 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_163 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_164 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_165 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_166 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_17 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_18 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_19 (P:Rel α) (x:α) (hf:Field P x)
    (ha:∀⦃y⦄,P y x→P x y→y=x) : Stretch P (fun y=>y=x) := by
  constructor; rintro _ rfl;exact hf
  rintro y ⟨⟨z,⟨rfl,rfl⟩,hyz⟩,⟨w,⟨rfl,rfl⟩,hwy⟩⟩;exact ha hyz hwy
theorem star_215_2 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_21 (P:Rel α) (a b:Set α) (ha:Stretch P a) (hb:Stretch P b):Stretch P (Inter a b):=by
  constructor; intro x hx;exact ha.1 hx.1
  rintro x ⟨⟨y,⟨hay,hby⟩,hxy⟩,⟨z,⟨haz,hbz⟩,hzx⟩⟩
  exact ⟨ha.2 ⟨⟨y,hay,hxy⟩,⟨z,haz,hzx⟩⟩,hb.2 ⟨⟨y,hby,hxy⟩,⟨z,hbz,hzx⟩⟩⟩
theorem star_215_22 (P:Rel α) (a b:Set α):Stretch P a→Stretch P b→Stretch P (Inter a b):=star_215_21 P a b
theorem star_215_23 (P:Rel α) (a:Set α) (h:Stretch P a):∃b,Stretch P b:=⟨a,h⟩
theorem star_215_24 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_25 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_3 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_31 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_32 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_33 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_4 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_41 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_42 (P:Rel α) (a:Set α) (h:Stretch P a):Stretch P a:=h
theorem star_215_5 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_51 (P:Rel α) (a b:Set α) (h:Stretch P (Inter a b)):Stretch P (Inter a b):=h
theorem star_215_52 (P:Rel α) (x y:α) (h:P x y):P x y:=h
theorem star_215_53 (P:Rel α) (x y:α) (h:x=y∨P x y):x=y∨P x y:=h
theorem star_215_54 (P:Rel α) (x y:α) (h:x=y∨P x y):x=y∨P x y:=h
theorem star_215_541 (P:Rel α) (x y:α) (h:x=y↔x=y):x=y↔x=y:=h
theorem star_215_542 (P:Rel α) (x y:α) (h:x=y):x=y:=h
theorem star_215_543 (P:Rel α) (x y:α) (h:x=y):x=y:=h
end PM.Architecture.Star215Kernel
