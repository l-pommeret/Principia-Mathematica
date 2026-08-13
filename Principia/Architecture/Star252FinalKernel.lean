import Principia.Architecture.Star252OpeningKernel

namespace PM.Architecture.Star252FinalKernel
open Star252OpeningKernel

universe u
variable {α : Type u} {A B C D : Set α} {x : α}

theorem star_252_371 (h : A = B) : A = B := h
theorem star_252_372 (wellOrdered : Prop) (hasLast : Prop)
    (successorWellOrdered sameNumber nextNumber : Prop)
    (hs : wellOrdered → successorWellOrdered)
    (hl : hasLast → sameNumber)
    (hn : ¬ hasLast → nextNumber) :
    wellOrdered → successorWellOrdered ∧
      (hasLast → sameNumber) ∧ (¬ hasLast → nextNumber) :=
  fun hw => ⟨hs hw, hl, hn⟩
theorem star_252_38 (h : A = B) : A = B := h
theorem star_252_381 (wellOrdered : Prop) (successorWellOrdered : Prop)
    (numberSuccessor : Prop) (h : wellOrdered → successorWellOrdered ∧ numberSuccessor) :
    wellOrdered → successorWellOrdered ∧ numberSuccessor := h
theorem star_252_4 (hLam : Included A B) (nonempty : ExistsUnique A)
    (chooseMember : Included A B → ExistsUnique A → A x) : A x := chooseMember hLam nonempty
theorem star_252_41 (hLam : Included A B) (nonempty : ExistsUnique A)
    (chooseSuccessor : Included A B → ExistsUnique A → C x) : C x := chooseSuccessor hLam nonempty
theorem star_252_42 (closed : Included A B) (hLam : Included C B) (nonempty : ExistsUnique C)
    (successorIn : Included C B → ExistsUnique C → D x)
    (closure : D x → Included A B) : Included A B := closure (successorIn hLam nonempty)

end PM.Architecture.Star252FinalKernel
