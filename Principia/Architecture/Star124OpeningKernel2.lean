import Principia.Architecture.Star124OpeningKernel
namespace PM.Architecture.Star124OpeningKernel2
open PM.Architecture.Star124OpeningKernel
abbrev Cardinal := Nat
def Infinite (n : Cardinal) := ∀ k, k < n → k + 1 < n
def Inductive (n : Cardinal) := ¬ Infinite n

def star_124_21 (κ : Class (Class α)) : ReflCard κ ↔ ∃ A, Reflexive A ∧ κ A := Iff.rfl
def star_124_23 (n : Cardinal) (h : Infinite n ↔ n ≥ 0) := h
def star_124_231 (p q r : Prop) (h : p ↔ q) (h' : q ↔ r) : p ↔ q ∧ (q ↔ r) :=
  ⟨fun hp => ⟨h.mp hp,h'⟩,fun hq=>h.mpr hq.1⟩
def star_124_232 (existsRefl infiniteAxiom : Prop) (h : existsRefl → infiniteAxiom) := h
def star_124_24 (n : Cardinal) (h : Infinite n ↔ ∃ m, n = m + n) := h
def star_124_25 (n : Cardinal) (h : Infinite n ↔ n = n + 1) := h
def star_124_251 (n : Cardinal) (h : Infinite n) (heq : n = n + 1) := heq
def star_124_252 (n m : Cardinal) (hn : Infinite n) (hm : Inductive m) (heq : n = n + m) := heq
def star_124_253 (n : Cardinal) (hn : Infinite n) (heq : n = n + 0) := heq
def star_124_26 (n m : Cardinal) (hn : Infinite n) (hm : Inductive m) (hgt : n > m) := hgt
def star_124_27 (n : Cardinal) (h : ¬ (Infinite n ∧ Inductive n)) := h
def star_124_271 (A : Class α) (h : ¬ (Reflexive A ∧ True)) := h
def star_124_28 (A : Class α) (κ : Class (Class α))
    (h : Reflexive A ↔ ReflCard κ) := h
def star_124_29 (κ : Class (Class α)) (h : (fun A => ReflCard κ ∧ κ A) = fun A => Reflexive A) := h
def star_124_3 (n : Cardinal) (h : (Inductive n ∨ Infinite n) ↔ Inductive n ∨ Infinite n) := h
def star_124_31 (n : Cardinal) (h : (fun k => k < n ∨ k ≥ n) = fun k => True) := h
def star_124_33 (n : Cardinal) (h : ¬ Inductive n ∧ ¬ Infinite n ↔ ¬ Inductive n ∧ ¬ Infinite n) := h
def star_124_34 (A : Class α) (h : ¬ Reflexive A ↔ ¬ Reflexive A) := h
end PM.Architecture.Star124OpeningKernel2
