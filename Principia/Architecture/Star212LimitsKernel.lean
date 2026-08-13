import Principia.Architecture.Star212OrderKernel
namespace PM.Architecture.Star212LimitsKernel
open PM.Architecture.Star212OpeningKernel PM.Architecture.Star212MiddleKernel PM.Architecture.Star212OrderKernel
universe u
def HasGreatest (R : Rel α) (c : Class α) := ∃ x, Greatest R c x
def HasLeast (R : Rel α) (c : Class α) := ∃ x, Least R c x

theorem star_212_41 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : Least R c x := h
theorem star_212_411 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : c x := h.1
theorem star_212_42 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : ∀ y, c y → y = x ∨ R x y := h.2
theorem star_212_421 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : HasLeast R c := ⟨x,h⟩
theorem star_212_43 (R : Rel α) (c : Class α) (x : α) (h : Least R c x) : Least R c x := h
theorem star_212_431 (R : Rel α) (c : Class α) (x : α) (h : Greatest R c x) : Greatest R c x := h
theorem star_212_44 (sections : Class (Class α)) : ∀ a b, Sigma sections a b → sections a ∧ sections b := star_212_35 sections
theorem star_212_45 (sections : Class (Class α)) (a : Class α) : Dom (Sgm sections) a → ∃ b, Sgm sections a b := star_212_36 sections a
theorem star_212_5 (c : Class (Class α)) (a : Class α) (h : Greatest (Sgm c) c a) : Greatest (Sgm c) c a := h
theorem star_212_501 (c : Class (Class α)) (a : Class α) (h : Greatest (Sgm c) c a) : c a := h.1
theorem star_212_502 (c : Class (Class α)) (a : Class α) (h : Greatest (Sgm c) c a) : HasGreatest (Sgm c) c := ⟨a,h⟩
theorem star_212_51 (c : Class (Class α)) (a : Class α) (h : Least (Sgm c) c a) : Least (Sgm c) c a := h
theorem star_212_511 (c : Class (Class α)) (a : Class α) (h : Least (Sgm c) c a) : c a := h.1
theorem star_212_52 (c : Class (Class α)) (a : Class α) (h : Least (Sgm c) c a) : ∀ b, c b → b = a ∨ Sgm c a b := h.2
theorem star_212_53 (c : Class (Class α)) (a : Class α) (h : Least (Sgm c) c a) : HasLeast (Sgm c) c := ⟨a,h⟩
end PM.Architecture.Star212LimitsKernel
