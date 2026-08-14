/-! # PM I, ✱62: membership relation, complete extensional kernel. -/
namespace PM.Architecture.Star62Kernel
abbrev Class (A : Sort u) := A → Prop
def Eps (x : A) (a : Class A) := a x
def Image (R : A→B→Prop) (a : Class A) : Class B := fun y => ∃x,a x∧R x y
def Domain (R : A→B→Prop) : Class A := fun x => ∃y,R x y
def ConverseDomain (R : A→B→Prop) : Class B := fun y => ∃x,R x y
def RestrictRight (R : A→B→Prop) (b:Class B) := fun x y => R x y∧b y
def Included (R S : A→B→Prop) := ∀x y,R x y→S x y
def Singleton (x:A) : Class A := fun y=>y=x
def One (a:Class A) := ∃x,a=Singleton x
def ExistsValue (a:Class A) := ∃x,∀y,a y↔y=x
def Value (a:Class A) (x:A) := ∀y,a y↔y=x
def EpsImage (a:Class A) : Class A := fun x => Eps x a

/-- ✱62·01. `ε = ẑxα(x ε α) Df`. -/
def star_62_01 (x : A) (a : Class A) : Prop := a x
theorem star_62_1 (x:A) (a:Class A) : Eps x a ↔ a x := Iff.rfl
theorem star_62_2 (a:Class A) : EpsImage a = a := rfl
theorem star_62_21 (x:A) : EpsImage (Singleton x) = Singleton x := rfl
theorem star_62_22 : Domain (@Eps A) = fun _=>True := by funext x; apply propext; exact ⟨fun _=>True.intro,fun _=>⟨Singleton x,rfl⟩⟩
theorem star_62_23 (a:Class A) : ConverseDomain Eps a ↔ ∃x,a x := Iff.rfl
theorem star_62_231 : ¬ ConverseDomain (@Eps A) (fun _=>False) := by rintro ⟨_,h⟩; exact h
theorem star_62_24 [Nonempty A] (a:Class A) : a = (fun _=>True) → ConverseDomain Eps a := by rintro rfl; exact ⟨Classical.choice inferInstance,True.intro⟩
theorem star_62_25 (a:Class A) : ConverseDomain Eps a ↔ ¬(a=fun _=>False) := by
  classical
  constructor
  · rintro ⟨x,hx⟩ h
    have := congrFun h x
    exact this.mp hx
  · intro h
    exact Classical.byContradiction fun q => h (by
      funext x
      apply propext
      exact ⟨fun hx=>(q ⟨x,hx⟩).elim,False.elim⟩)
theorem star_62_26 (R:A→B→Prop) : RestrictRight R (fun _=>True)=R := by funext x y; apply propext; simp [RestrictRight]
theorem star_62_3 (a:Class A) : EpsImage a = a := rfl
theorem star_62_31 (x:A) : Eps x = fun a:Class A=>a x := rfl
theorem star_62_32 (x:A) (a:Class A) : Eps x a ↔ a x := Iff.rfl
theorem star_62_33 (x:A) (a:Class A) : ¬ Eps x a ↔ ¬ a x := Iff.rfl
theorem star_62_34 (P:B→A→Prop) (b:B) (a:Class A) : (∃x,a x∧P b x) ↔ Image (fun x b=>P b x) a b := Iff.rfl
theorem star_62_4 (x:A) (a:Class A) : RestrictRight Eps (PM.Architecture.Star62Kernel.Singleton a) x a ↔ a x := by simp [RestrictRight,Singleton,Eps]
theorem star_62_41 (x:A) : Eps x (Singleton x) := rfl
theorem star_62_42 (x:A) (a:Class A) : a x → Eps x a := id
theorem star_62_43 (x:A) : Domain (RestrictRight Eps (Singleton (Singleton x))) x := ⟨Singleton x,rfl,rfl⟩
theorem star_62_44 (R:A→Class A→Prop) : Included R Eps ↔ ∀x a,R x a→a x := Iff.rfl
theorem star_62_45 (R:A→Class A→Prop) : Included R Eps → ∀x a,R x a→Eps x a := id
theorem star_62_5 : Included (fun (x:A) (a:Class A)=>a=PM.Architecture.Star62Kernel.Singleton x) Eps := by rintro x a rfl; rfl
theorem star_62_51 (a:Class A) (x:A) : Value a x → a x := fun h=>(h x).2 rfl
theorem star_62_52 (a:Class A) : ExistsValue a ↔ One a := by
  constructor
  · rintro ⟨x,h⟩
    refine ⟨x, ?_⟩
    funext y
    exact propext (h y)
  · rintro ⟨x,rfl⟩
    exact ⟨x,fun _=>Iff.rfl⟩
theorem star_62_53 (a:Class A) (x:A) : Value a x → a=Singleton x := by intro h; funext y; exact propext (h y)
theorem star_62_54 (a:Class A) : One a → ∃x,Value a x := fun h => (star_62_52 a).mpr h
theorem star_62_55 (x:A) : Value (Singleton x) x := fun _=>Iff.rfl
theorem star_62_56 (a:Class A) : EpsImage a=a := star_62_2 a
theorem star_62_57 (x:A) (a:Class A) : Eps x a↔a x := Iff.rfl
end PM.Architecture.Star62Kernel
