import Principia.Architecture.Star254MiddleKernel

/-! # PM III ✱254·244–✱254·433 — next exact local-source tranche. -/
namespace PM.Architecture.Star254NextKernel
open PM.Architecture.Star254OpeningKernel
open PM.Architecture.Star254MiddleKernel

theorem support_254_244 {P Q : Type u} (e : Iso P Q) : Similar P Q := ⟨e⟩
theorem support_254_245 {P Q : Type u} : Similar P Q → Similar Q P := fun ⟨e⟩ => ⟨isoSymm e⟩
theorem support_254_25 {P Q R : Type u} : Similar P Q → Similar Q R → Similar P R := fun ⟨e⟩ ⟨f⟩ => ⟨isoTrans e f⟩
theorem support_254_26 (P : Type u) : Similar P P := ⟨isoRefl P⟩
theorem support_254_261 {P Q : Type u} (e : Iso P Q) (x : P) : e.invFun (e.toFun x) = x := e.left_inv x
theorem support_254_27 {P Q : Type u} (h : Less P Q) : Less P Q := h
theorem support_254_31 {P Q : Type u} : Similar P Q ↔ Nonempty (Iso P Q) := Iff.rfl
theorem support_254_311 {P Q : Type u} : Similar P Q → Nonempty (Iso Q P) := fun ⟨e⟩ => ⟨isoSymm e⟩
theorem support_254_32 {P Q R : Type u} : Similar P Q → Similar Q R → Similar P R := support_254_25
theorem support_254_321 {P Q R : Type u} (e : Iso P Q) (f : Iso Q R) : Similar P R := ⟨isoTrans e f⟩
theorem support_254_33 (P Q : Type u) : Similar P Q ↔ Similar Q P := star_254_223 P Q
theorem support_254_35 {P Q : Type u} (h : Less P Q) : Nonempty (P → Q) := by rcases h with ⟨f,_,_⟩; exact ⟨f⟩
theorem support_254_36 {P Q : Type u} (h : Less P Q) : Nonempty (P → Q) := by rcases h with ⟨f,_,_⟩; exact ⟨f⟩
theorem support_254_37 {P Q : Type u} (h : Similar P Q) : Nonempty (P → Q) := by rcases h with ⟨e⟩; exact ⟨e.toFun⟩
theorem star_254_42 {P Q : Type u} (e : Iso P Q) : Similar P Q := ⟨e⟩
theorem star_254_43 {P Q : Type u} (h : Similar P Q) : Similar Q P := (star_254_223 P Q).mp h
theorem star_254_431 {P Q R : Type u} (h : Similar P Q) (k : Similar Q R) : Similar P R := support_254_25 h k
theorem star_254_433 {P Q : Type u} (e : Iso P Q) (x : P) : e.invFun (e.toFun x) = x := e.left_inv x

end PM.Architecture.Star254NextKernel
