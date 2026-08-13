import Principia.Architecture.Star116SecondKernel

namespace PM.Architecture.Star116ThirdKernel
open Star116SecondKernel

def UniqueType (A : Type u) := ∃ x : A, ∀ y, y = x
def EmptyType (A : Type u) := ∀ x : A, False
inductive Zero where
inductive One where | unit

theorem star_116_24 (A : Type u) (B : Type v) : CardinalExp A B = CardinalClass (B → A) := rfl
theorem star_116_25 (A : Type u) (B : Type v) : CardinalExp A B = CardinalClass (B → A) := rfl
theorem star_116_251 (A : Type u) (B : Type v) : CardinalExp A B (B → A) :=
  ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩
theorem star_116_26 : SimilarType A C → SimilarType B D → SimilarType (B → A) (D → C) := star_116_19
theorem star_116_261 (A : Type u) (B : Type v) : SimilarType (B → A) (B → A) :=
  ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩
theorem star_116_27 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_271 (A : Type u) (B : Type v) : CardinalExp A B (B → A) := star_116_251 A B

theorem star_116_3 (A : Type u) : UniqueType (Zero → A) := by
  let f : Zero → A := fun x => nomatch x
  exact ⟨f, fun g => funext fun x => nomatch x⟩
theorem star_116_301 (A : Type u) : UniqueType (Zero → A) := star_116_3 A
theorem star_116_31 (B : Type v) [Nonempty B] : EmptyType (B → Zero) := by
  intro f
  let b : B := Classical.choice inferInstance
  exact nomatch f b
theorem star_116_311 (B : Type v) [Nonempty B] : EmptyType (B → Zero) := star_116_31 B
theorem star_116_32 (A : Type u) : SimilarType (One → A) A := by
  exact ⟨⟨fun f => f One.unit, fun a _ => a,
    fun f => funext fun x => by cases x; rfl, fun _ => rfl⟩⟩
theorem star_116_321 (A : Type u) : SimilarType (One → A) A := star_116_32 A
theorem star_116_33 (B : Type v) : UniqueType (B → One) := by
  exact ⟨fun _ => One.unit, fun f => funext fun b => by cases f b; rfl⟩
theorem star_116_331 (B : Type v) : UniqueType (B → One) := star_116_33 B
theorem star_116_34 (A : Type u) : SimilarType (Bool → A) (A × A) := by
  exact ⟨⟨fun f => (f false, f true), fun p b => cond b p.2 p.1,
    fun f => funext fun b => by cases b <;> rfl, fun p => by cases p; rfl⟩⟩
theorem star_116_35 (A : Type u) (B : Type v) [Nonempty B] :
    EmptyType (B → A) ↔ EmptyType A := by
  constructor
  · intro h a
    let f : B → A := fun _ => a
    exact h f
  · intro h f
    let b : B := Classical.choice inferInstance
    exact h (f b)
theorem star_116_351 (A : Type u) : UniqueType (Zero → A) := star_116_3 A

end PM.Architecture.Star116ThirdKernel
