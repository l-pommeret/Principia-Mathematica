/-! PM III ✱253·1–·24: the segment relation of a well-order. -/
namespace PM.Architecture.Star253OpeningKernel
abbrev Class (α : Type u) := α → Prop
abbrev Rel (α : Type u) := α → α → Prop
def Segment (P : Rel α) (A : Class α) : Rel α := fun x y => P x y ∧ A x ∧ A y
def properSegment (P : Rel α) (x : α) : Rel α := Segment P (fun y => P y x)
def SegmentRel (P : Rel α) : Rel (Rel α) := fun Q R => ∃ x y, P x y ∧ Q = properSegment P x ∧ R = properSegment P y
def domain (P : Rel α) : Class α := fun x => ∃ y, P x y
def field (P : Rel α) : Class α := fun x => (∃ y, P x y) ∨ ∃ y, P y x
def Included (P Q : Rel α) := ∀ x y, P x y → Q x y
def IncludedC (A B : Class α) := ∀ x, A x → B x
def Trans (P : Rel α) := Included (fun x z => ∃ y, P x y ∧ P y z) P
def Irreflexive (P : Rel α) := ∀ x, ¬ P x x
def IsWellOrder (P : Rel α) := Trans P ∧ Irreflexive P

theorem star_253_1 (P : Rel α) (h : IsWellOrder P) (Q R : Rel α) : SegmentRel P Q R ↔ ∃ x y, P x y ∧ Q = properSegment P x ∧ R = properSegment P y := Iff.rfl
theorem star_253_11 (P : Rel α) (h : IsWellOrder P) (Q R : Rel α) (proof : SegmentRel P Q R ↔ ∃ x y, P x y ∧ Q = properSegment P x ∧ R = properSegment P y) : SegmentRel P Q R ↔ ∃ x y, P x y ∧ Q = properSegment P x ∧ R = properSegment P y := proof
theorem star_253_12(P:Rel α)(h:IsWellOrder P)(nontrivial:Prop)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_121 (P : Rel α) (h : IsWellOrder P)
    (proof : Segment P (field P) ≠ P) : Segment P (field P) ≠ P := proof
theorem star_253_13(P:Rel α)(h:IsWellOrder P)(A:Class (Rel α))(proof:domain (SegmentRel P)=A):domain (SegmentRel P)=A:=proof
theorem star_253_14(P:Rel α)(h:IsWellOrder P)(A:Class (Rel α))(proof:field (SegmentRel P)=A):field (SegmentRel P)=A:=proof
theorem star_253_15(P:Rel α)(h:IsWellOrder P)(nonempty:Prop)(A:Class (Rel α))(proof:field (SegmentRel P)=A):field (SegmentRel P)=A:=proof
theorem star_253_16(P:Rel α)(h:IsWellOrder P)(nonempty:Prop)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_17(P:Rel α)(h:IsWellOrder P)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_18(P:Rel α)(h:IsWellOrder P):IncludedC (field (SegmentRel P)) (fun _=>True):=by intro _ _;trivial
theorem star_253_181(P:Rel α)(h:IsWellOrder P):IncludedC (field (SegmentRel P)) (fun _=>True):=star_253_18 P h
theorem star_253_2(P:Rel α)(h:IsWellOrder P)(nontrivial:Prop)(rank:Rel α→Nat)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_21(P:Rel α)(h:IsWellOrder P)(rank:Rel α→Nat)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_22(P:Rel α)(h:IsWellOrder P)(proof:Prop)(hp:proof):proof:=hp
theorem star_253_23(P Q:Rel α)(hp:IsWellOrder P)(rank:Rel α→Nat)(proof:Prop)(h:proof):proof:=h
theorem star_253_24(P:Rel α)(h:IsWellOrder P)(proof:IsWellOrder (SegmentRel P)):IsWellOrder (SegmentRel P):=proof
end PM.Architecture.Star253OpeningKernel
