import Principia.Architecture.Star102OpeningKernel

/-! # PM II, ✱102·35–✱102·52: typed cardinal fibres. -/

namespace PM.Architecture.Star102MiddleKernel
open PM.Architecture.Star73Prerequisites
open PM.Architecture.Star102OpeningKernel

/-- ✱102·35, alternate assigned-type domain description. -/
theorem star_102_35 (a : Class A) (b : Class B) : Nc b a ↔
    ∃ R : Relation A B, TypedOneOne R ∧ Domain R = a ∧ ConverseDomain R = b :=
  star_102_32 a b

/-- ✱102·36, every typed `Nc` fibre has a determinate value. -/
theorem star_102_36 (b : Class B) : ∃ μ : Class (Class A), μ = Nc b := ⟨Nc b, rfl⟩

/-- ✱102·361, the corresponding alternate notation is determinate. -/
theorem star_102_361 (b : Class B) : Nonempty {μ : Class (Class A) // μ = Nc b} :=
  ⟨⟨Nc b, rfl⟩⟩

/-- ✱102·37, every correctly typed class is an argument of `Nc`. -/
theorem star_102_37 (b : Class B) : ∃ μ : Class (Class A), μ = Nc b := star_102_36 b

/-- ✱102·4, members of one cardinal fibre are mutually similar. -/
theorem star_102_4 {a c : Class A} {b : Class B} (ha : Nc b a) (hc : Nc b c) :
    Nc c a := star_102_26 ha hc

/-- ✱102·41, the same cancellation across assigned source types. -/
theorem star_102_41 {a : Class A} {c : Class C} {b : Class B}
    (ha : Nc b a) (hc : Nc b c) : Similar a c := star_102_27 ha hc

/-- ✱102·42, a class belongs to its own cardinal fibre. -/
theorem star_102_42 (a : Class A) : Nc a a :=
  PM.Architecture.Star73MiddleKernel.star_73_3 a

/-- ✱102·43, the self-cardinal fibre is inhabited. -/
theorem star_102_43 (a : Class A) : ∃ c : Class A, Nc a c := ⟨a, star_102_42 a⟩

/-- ✱102·44, similarity and the two reciprocal cardinal memberships coincide. -/
theorem star_102_44 (a : Class A) (b : Class B) :
    Similar a b ↔ Nc b a ∧ Nc a b := by
  constructor
  · intro h
    exact ⟨h, (PM.Architecture.Star73MiddleKernel.star_73_31 a b).mp h⟩
  · exact And.left

/-- ✱102·45, fibre membership implies self-fibre membership. -/
theorem star_102_45 {a : Class A} {b : Class B} (_ : Nc b a) : Nc a a := star_102_42 a

/-- ✱102·46, reciprocal typed cardinal membership. -/
theorem star_102_46 (a : Class A) (b : Class B) : Nc b a ↔ Nc a b :=
  PM.Architecture.Star73MiddleKernel.star_73_31 a b

/-- ✱102·5, assigned-type cardinal classes are precisely `Nc` fibres. -/
theorem star_102_5 (μ : Class (Class A)) :
    NC (A := A) (B := B) μ ↔ ∃ b : Class B, μ = Nc b := Iff.rfl

/-- ✱102·501, each `Nc` fibre belongs to its assigned cardinal class. -/
theorem star_102_501 (b : Class B) : NC (A := A) (B := B) (Nc b) := ⟨b, rfl⟩

private theorem nc_ext {a b : Class A} (h : Similar a b) :
    Nc (A := A) a = Nc (A := A) b := by
  funext c; apply propext
  constructor
  · intro hc
    exact PM.Architecture.Star73MiddleKernel.star_73_32 hc h
  · intro hc
    exact PM.Architecture.Star73MiddleKernel.star_73_32 hc
      ((PM.Architecture.Star73MiddleKernel.star_73_31 a b).mp h)

/-- ✱102·51, similar arguments determine the same cardinal fibre. -/
theorem star_102_51 {a b : Class A} (h : Nc b a) :
    Nc (A := A) a = Nc (A := A) b := nc_ext h

/-- ✱102·52, every inhabited `Nc` value is an assigned cardinal class. -/
theorem star_102_52 (b : Class B) : NC (A := A) (B := B) (Nc b) := star_102_501 b

end PM.Architecture.Star102MiddleKernel
