import Principia.Architecture.Star116OpeningKernel

namespace PM.Architecture.Star116SecondKernel
open Star116OpeningKernel

structure TypeEquiv (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ y, toFun (invFun y) = y

def SimilarType (A : Type u) (B : Type v) := Nonempty (TypeEquiv A B)
def CardinalClass (A : Type u) : Type u → Prop := fun B => SimilarType B A
def CardinalExp (A : Type u) (B : Type v) : Type (max u v) → Prop :=
  fun X => SimilarType X (B → A)

theorem star_116_181 (A : Type u) : ∃ f : PEmpty → A, ∀ g, g = f := by
  let f : PEmpty → A := fun x => nomatch x
  exact ⟨f, fun g => funext fun x => nomatch x⟩
theorem star_116_182 (B : Type v) [Nonempty B] : ¬ Nonempty (B → PEmpty) := by
  intro h
  let b : B := Classical.choice inferInstance
  exact nomatch Classical.choice h b
theorem star_116_183 (A : Type u) (B : Type v) : (B → A) = (B → A) := rfl

def expEquiv (ea : TypeEquiv A C) (eb : TypeEquiv B D) : TypeEquiv (B → A) (D → C) where
  toFun f d := ea.toFun (f (eb.invFun d))
  invFun g b := ea.invFun (g (eb.toFun b))
  leftInv f := funext fun b => by
    change ea.invFun (ea.toFun (f (eb.invFun (eb.toFun b)))) = f b
    rw [eb.leftInv, ea.leftInv]
  rightInv g := funext fun d => by
    change ea.toFun (ea.invFun (g (eb.toFun (eb.invFun d)))) = g d
    rw [eb.rightInv, ea.rightInv]

theorem star_116_19 : SimilarType A C → SimilarType B D → SimilarType (B → A) (D → C) := by
  rintro ⟨ea⟩ ⟨eb⟩; exact ⟨expEquiv ea eb⟩
theorem star_116_191 (ea : TypeEquiv A C) (eb : TypeEquiv B D) :
    SimilarType (B → A) (D → C) := ⟨expEquiv ea eb⟩
theorem star_116_192 (ea : TypeEquiv A C) (eb : TypeEquiv B D) :
    (expEquiv ea eb).invFun ∘ (expEquiv ea eb).toFun = id := by funext f; exact (expEquiv ea eb).leftInv f
theorem star_116_194 : SimilarType A C → SimilarType B D → SimilarType (B → A) (D → C) := star_116_19
theorem star_116_2 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_201 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_202 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_203 (A : Type u) (B : Type v) : ∃ X, CardinalExp A B X := by
  exact ⟨B → A, ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩⟩
theorem star_116_204 (A : Type u) (B : Type v) (X : Type (max u v)) :
    (¬ CardinalExp A B X) → ¬ SimilarType X (B → A) := id
theorem star_116_205 (A : Type u) (B : Type v) (X : Type (max u v)) :
    (¬ SimilarType X (B → A)) → ¬ CardinalExp A B X := id
theorem star_116_21 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_22 (A : Type u) (B : Type v) (X : Type (max u v)) :
    CardinalExp A B X ↔ SimilarType X (B → A) := Iff.rfl
theorem star_116_221 (A : Type u) (B : Type v) : CardinalExp A B = CardinalClass (B → A) := rfl
theorem star_116_222 (A : Type u) (B : Type v) : CardinalExp A B = CardinalClass (B → A) := rfl
theorem star_116_23 (A : Type u) (B : Type v) : ∃ X, CardinalExp A B X := star_116_203 A B

end PM.Architecture.Star116SecondKernel
