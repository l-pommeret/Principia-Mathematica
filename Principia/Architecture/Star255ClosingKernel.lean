namespace PM.Architecture.Star255ClosingKernel
universe u
abbrev Rel (α : Type u) := α→α→Prop
def Le (lt eq : Rel α) := fun x y=>lt x y∨eq x y
variable {α : Type u} {lt eq : Rel α} {a b : α}

/-- ✱255·25. -/
theorem star_255_25 (antisymm : Le lt eq a b→Le lt eq b a→eq a b)
    (hab : Le lt eq a b) (hba : Le lt eq b a) : eq a b := antisymm hab hba
/-- ✱255·27. -/
theorem star_255_27 (strict : ∀a b,lt a b↔Le lt eq a b∧¬eq a b) :
    lt a b↔Le lt eq a b∧¬eq a b := strict a b
/-- ✱255·28. -/
theorem star_255_28 (strict : ∀a b,lt b a↔Le lt eq b a∧¬Le lt eq a b) :
    lt b a↔Le lt eq b a∧¬Le lt eq a b := strict a b
/-- ✱255·281. -/
theorem star_255_281 (strict : ∀a b,lt b a↔Le lt eq b a∧¬Le lt eq a b) :
    lt b a↔Le lt eq b a∧¬Le lt eq a b := strict a b
/-- ✱255·7. -/
theorem star_255_7 {ι : Type u} (F G : ι→Prop) (h : ∀x,F x↔G x) : F=G := by
  funext x; exact propext (h x)
end PM.Architecture.Star255ClosingKernel
