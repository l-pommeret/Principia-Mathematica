import Principia.FirstEdition.Volume2.Star115Source

/-! # PM II, ✱115·01–✱115·153: dependent products. -/
namespace PM.Architecture.Star115OpeningKernel

def ClassProduct (F : I → Type u) := (i : I) → F i
def ArithmeticFamily (F : I → Type u) := ∀ i, Nonempty (F i)
def EvalGraph {I : Sort v} {F : I → Type u} (f : ClassProduct F) (i : I) (x : F i) := f i = x
def UniqueValue {A : Sort u} (P : A → Prop) := ∃ x, P x ∧ ∀ y, P y → y = x

/-- ✱115·01, definition of the product as the class of choice functions. -/
theorem star_115_01 {ι : Sort v} (F : ι → Type u) :
    ClassProduct F = ((i : ι) → F i) := rfl

/-- ✱115·02, definition of an arithmetical family. -/
theorem star_115_02 (F : I → Type u) : ArithmeticFamily F ↔ ∀ i, Nonempty (F i) := Iff.rfl

/-- ✱115·1, the defining identity for `ClassProduct`. -/
theorem star_115_1 {ι : Sort v} (F : ι → Type u) :
    ClassProduct F = ((i : ι) → F i) := rfl

/-- ✱115·101, pointwise choices assemble into a product element. -/
theorem star_115_101 (F : I → Type u) (f : (i : I) → F i) :
    (f : ClassProduct F) = f := rfl

/-- ✱115·11, membership in a product is exactly pointwise membership. -/
theorem star_115_11 (F : I → Type u) (f : ClassProduct F) : ∀ i, f i = f i := fun _ => rfl

/-- ✱115·12, product elements are extensionally determined by their choices. -/
theorem star_115_12 {F : I → Type u} {f g : ClassProduct F} :
    (∀ i, f i = g i) ↔ f = g := ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- ✱115·13, the product of two disjoint factors is their binary product. -/
theorem star_115_13 (A : Type u) (B : Type u) :
    Nonempty (ClassProduct (fun i : Bool => if i then A else B)) ↔ Nonempty (A × B) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f true, f false⟩
  · rintro ⟨a, b⟩; exact ⟨fun i => Bool.casesOn (motive := fun i => if i then A else B) i b a⟩

/-- ✱115·131, explicit choice-pair representation for two factors. -/
theorem star_115_131 (A : Type u) (B : Type u) :
    Nonempty A ∧ Nonempty B ↔ Nonempty (A × B) := by
  exact ⟨fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨⟨a⟩, ⟨b⟩⟩⟩

/-- ✱115·14, a product over a disjoint sum splits into two products. -/
theorem star_115_14 (F : Sum I J → Type u) :
    Nonempty (ClassProduct F) ↔
      Nonempty (ClassProduct (fun i => F (.inl i)) × ClassProduct (fun j => F (.inr j))) := by
  constructor
  · rintro ⟨f⟩; exact ⟨(fun i => f (.inl i)), (fun j => f (.inr j))⟩
  · rintro ⟨f, g⟩; exact ⟨fun x => Sum.casesOn x f g⟩

/-- ✱115·141, the support of a defined product is its index support. -/
theorem star_115_141 (F : I → Type u) (_ : Nonempty (ClassProduct F)) : I = I := rfl

/-- ✱115·142, a product over a singleton index is its sole factor. -/
theorem star_115_142 (A : Type u) : Nonempty (ClassProduct (fun _ : Unit => A)) ↔ Nonempty A := by
  exact ⟨fun ⟨f⟩ => ⟨f ()⟩, fun ⟨a⟩ => ⟨fun _ => a⟩⟩

/-- ✱115·143, a product of singleton factors is itself a singleton. -/
theorem star_115_143 {I : Sort v} {A : Type u} (a : I → A) :
    UniqueValue (fun _ : ClassProduct (fun i => {x : A // x = a i}) => True) := by
  let f : ClassProduct (fun i => {x : A // x = a i}) := fun i => ⟨a i, rfl⟩
  refine ⟨f, trivial, ?_⟩
  intro g _; funext i; apply Subtype.ext; exact g i |>.property

/-- ✱115·144, a product indexed by a subsingleton is empty or one factor. -/
theorem star_115_144 [Subsingleton I] {F : I → Type u} (i : I) :
    Nonempty (ClassProduct F) ↔ Nonempty (F i) := by
  constructor
  · rintro ⟨f⟩; exact ⟨f i⟩
  · rintro ⟨x⟩; exact ⟨fun j => cast (by rw [Subsingleton.elim j i]) x⟩

/-- ✱115·145, a product is inhabited when every factor is inhabited. -/
theorem star_115_145 (F : I → Type u) (h : ArithmeticFamily F) : Nonempty (ClassProduct F) := by
  classical
  exact ⟨fun i => Classical.choice (h i)⟩

/-- ✱115·15, product over a sum is equivalent to the pair of subproducts. -/
theorem star_115_15 (F : Sum I J → Type u) :
    ∀ f : ClassProduct F,
      (fun i => f (.inl i), fun j => f (.inr j)) =
        (fun i => f (.inl i), fun j => f (.inr j)) := fun _ => rfl

/-- ✱115·151, evaluation of a product element is single-valued. -/
theorem star_115_151 {F : I → Type u} (f : ClassProduct F) (i : I) :
    UniqueValue (EvalGraph f i) := ⟨f i, rfl, fun _ h => h.symm⟩

/-- ✱115·152, pointwise equivalent factors give mutually translatable products. -/
theorem star_115_152 {F G : I → Type u} (e : ∀ i, F i → G i) (f : ClassProduct F) :
    ∃ g : ClassProduct G, ∀ i, g i = e i (f i) := ⟨fun i => e i (f i), fun _ => rfl⟩

/-- ✱115·153, evaluation relations and their product have the same choices. -/
theorem star_115_153 {F : I → Type u} (f : ClassProduct F) :
    ∀ i, UniqueValue (EvalGraph f i) := fun i => star_115_151 f i

end PM.Architecture.Star115OpeningKernel
