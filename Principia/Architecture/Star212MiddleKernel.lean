import Principia.Architecture.Star212OpeningKernel
namespace PM.Architecture.Star212MiddleKernel
open PM.Architecture.Star212OpeningKernel
universe u
def Converse (R : Rel α) : Rel α := fun a b => R b a
def Subrel (R S : Rel α) := ∀ a b, R a b → S a b
def Transitive (R : Rel α) := ∀ a b d, R a b → R b d → R a d
def ConnexOn (c : Class α) (R : Rel α) := ∀ a b, c a → c b → a = b ∨ R a b ∨ R b a

theorem star_212_151 : Sgm (fun _ => False : Class (Class α)) = EmptyRel := star_212_134
theorem star_212_152 (c : Class (Class α)) : Cod (Sgm c) = fun b => c b ∧ ∃ a, c a ∧ Proper a b := by
  funext b; apply propext; constructor
  · rintro ⟨a,ha,hb,hp⟩; exact ⟨hb,a,ha,hp⟩
  · rintro ⟨hb,a,ha,hp⟩; exact ⟨a,ha,hb,hp⟩
theorem star_212_153 (c : Class (Class α)) : AtMostOne c → AtMostOne (Cod (Sgm c)) := by
  intro hc a b ha hb
  apply hc
  · rcases ha with ⟨x,h⟩; exact h.2.1
  · rcases hb with ⟨x,h⟩; exact h.2.1
theorem star_212_154 (c : Class (Class α)) : (∀ b, Cod (Sgm c) b → c b) := by rintro b ⟨a,h⟩; exact h.2.1
theorem star_212_155 (c : Class (Class α)) : (∀ a, ¬Sgm c a a) := by intro a h; exact h.2.2.2 (fun _ hx => hx)
theorem star_212_156 (c : Class (Class α)) (a : Class α) : Cod (Sgm c) a → c a := star_212_154 c a
theorem star_212_16 (c : Class (Class α)) (top : Class α) (ht : c top) (hmax : ∀ a, c a → Included a top) :
    ∀ a, c a → a = top ∨ Sgm c a top := by
  intro a ha; by_cases h : a = top
  · exact Or.inl h
  · exact Or.inr ⟨ha,ht,hmax a ha,fun q => h (by funext x; exact propext ⟨fun hx => hmax a ha x hx,fun hx => q x hx⟩)⟩
theorem star_212_161 (c : Class (Class α)) (top : Class α) (ht : c top) : ∃ a, c a := ⟨top,ht⟩
theorem star_212_162 (c : Class (Class α)) : Dom (Sgm c) = fun a => c a ∧ ∃ b, c b ∧ Proper a b := star_212_132 c
theorem star_212_17 (sections : Class (Class α)) : Sigma sections = SegmentRel sections := rfl
theorem star_212_171 (sections : Class (Class α)) :
    Dom (Sigma sections) = (fun a => sections a ∧ ∃ b, sections b ∧ Proper a b) := star_212_132 sections
theorem star_212_172 (sections : Class (Class α)) : ∀ a, Field (Sigma sections) a → sections a := star_212_141 sections
theorem star_212_173 (sections : Class (Class α)) (a : Class α) : Field (Sigma sections) a → sections a := star_212_141 sections a
theorem star_212_18 (sections : Class (Class α)) : Converse (Sigma sections) = fun a b => sections b ∧ sections a ∧ Proper b a := rfl
theorem star_212_181 (sections : Class (Class α)) : Subrel (Converse (Sigma sections)) (Converse (SegmentRel sections)) := fun _ _ h => h
theorem star_212_2 (c sections : Class (Class α)) (h : ∀ a, c a → sections a) :
    Subrel (Sgm c) (Sigma c) ∧ Subrel (Sgm c) (Sigma sections) := by
  constructor
  · intro a b q; exact q
  · intro a b q; exact ⟨h a q.1,h b q.2.1,q.2.2⟩
theorem star_212_21 (c sections : Class (Class α)) (h : ∀ a, c a → sections a) : Subrel (Sigma c) (Sigma sections) := by
  intro a b q; exact ⟨h a q.1,h b q.2.1,q.2.2⟩
theorem star_212_22 (c : Class (Class α)) : Sgm c = fun a b => c a ∧ c b ∧ Proper a b := rfl
end PM.Architecture.Star212MiddleKernel
