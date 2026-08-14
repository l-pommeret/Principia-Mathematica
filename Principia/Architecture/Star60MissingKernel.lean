import Principia.Architecture.Star60Kernel

namespace PM.Architecture.Star60MissingKernel
open PM.Architecture.Star60Kernel
universe u

private theorem ext {a b : Class α} (h : ∀x,a x↔b x) : a=b := by funext x; exact propext (h x)

/-- ✱60·01, defining equation. -/
def star_60_01 (a : Class α) : Class (Class α) := fun b=>Included b a
/-- ✱60·321. -/
theorem star_60_321 (a : Class α) : a=PM.Architecture.Star60Kernel.Empty ↔ Cl a=PM.Architecture.Star60Kernel.Singleton a := by
  constructor
  · rintro rfl; exact star_60_32
  · intro h; have he : Cl a PM.Architecture.Star60Kernel.Empty := star_60_3 a; rw [h] at he; exact he.symm
/-- ✱60·33. -/
theorem star_60_33 : ClEx (PM.Architecture.Star60Kernel.Empty : Class α)=PM.Architecture.Star60Kernel.Empty := by
  apply ext; intro a; constructor
  · rintro ⟨hi,x,hx⟩; exact (hi x hx).elim
  · exact False.elim
/-- ✱60·36. -/
theorem star_60_36 (a : Class α) : Proper a→Proper (ClEx a) := fun h=>⟨a,star_60_35 a h⟩
/-- ✱60·361. -/
theorem star_60_361 (a : Class α) : Proper a↔Proper (ClEx a) := by
  exact ⟨star_60_36 a,fun ⟨b,hb⟩=>let ⟨x,hx⟩:=hb.2; ⟨x,hb.1 x hx⟩⟩
/-- ✱60·362. -/
theorem star_60_362 (x : α) :
    Cl (PM.Architecture.Star60Kernel.Singleton x)=Union (PM.Architecture.Star60Kernel.Singleton PM.Architecture.Star60Kernel.Empty) (PM.Architecture.Star60Kernel.Singleton (PM.Architecture.Star60Kernel.Singleton x)) := by
  apply ext; intro a; constructor
  · intro ha; by_cases hp : Proper a
    · right; apply ext; intro z; constructor
      · exact ha z
      · intro hzx; rcases hp with ⟨y,hy⟩; have hyx := ha y hy
        have hx : a x := hyx ▸ hy
        exact hzx ▸ hx
    · left; apply ext; intro z; exact ⟨fun hz=>(hp ⟨z,hz⟩).elim,False.elim⟩
  · rintro (rfl|rfl); exact star_60_3 _; exact fun _ h=>h
/-- ✱60·371. -/
theorem star_60_371 (a : Class α) (x : α) (h : a=PM.Architecture.Star60Kernel.Singleton x) :
    Included (Cl a) (Union (PM.Architecture.Star60Kernel.Singleton PM.Architecture.Star60Kernel.Empty) (PM.Architecture.Star60Kernel.Singleton a)) := by
  rw [h,star_60_362]; exact fun _ h=>h
/-- ✱60·38. -/
theorem star_60_38 (a : Class α) :
    (∃x,a=PM.Architecture.Star60Kernel.Singleton x) ↔ ClEx a=PM.Architecture.Star60Kernel.Singleton a := by
  constructor
  · rintro ⟨x,rfl⟩; exact star_60_37 x
  · intro h
    have haa : ClEx a a := by rw [h]; exact rfl
    rcases haa.2 with ⟨x,hx⟩
    have hs : ClEx a (PM.Architecture.Star60Kernel.Singleton x) :=
      ⟨fun y hy => hy ▸ hx, x, rfl⟩
    rw [h] at hs
    exact ⟨x,hs.symm⟩
/-- ✱60·39, every subset of a two-point class is one of the four displayed classes. -/
theorem star_60_39 (x y : α) : Cl (Union (PM.Architecture.Star60Kernel.Singleton x) (PM.Architecture.Star60Kernel.Singleton y)) =
    (Union (PM.Architecture.Star60Kernel.Singleton PM.Architecture.Star60Kernel.Empty) (Union (PM.Architecture.Star60Kernel.Singleton (PM.Architecture.Star60Kernel.Singleton x))
      (Union (PM.Architecture.Star60Kernel.Singleton (PM.Architecture.Star60Kernel.Singleton y)) (PM.Architecture.Star60Kernel.Singleton (Union (PM.Architecture.Star60Kernel.Singleton x) (PM.Architecture.Star60Kernel.Singleton y)))))) := by
  apply ext; intro a; constructor
  · intro ha; by_cases hx : a x <;> by_cases hy : a y
    · right; right; right; apply ext; intro z; exact ⟨ha z,fun h=>h.elim (fun e=>e ▸ hx) (fun e=>e ▸ hy)⟩
    · right; left; apply ext; intro z; exact ⟨fun hz=>(ha z hz).elim id (fun e=>(hy (e ▸ hz)).elim),fun e=>e ▸ hx⟩
    · right; right; left; apply ext; intro z; exact ⟨fun hz=>(ha z hz).elim (fun e=>(hx (e ▸ hz)).elim) id,fun e=>e ▸ hy⟩
    · left; apply ext; intro z; exact ⟨fun hz=>(ha z hz).elim (fun e=>(hx (e ▸ hz)).elim) (fun e=>(hy (e ▸ hz)).elim),False.elim⟩
  · rintro (rfl|rfl|rfl|rfl)
    · exact fun _ h=>h.elim
    · exact fun z hz=>Or.inl hz
    · exact fun z hz=>Or.inr hz
    · exact fun _ h=>h
/-- ✱60·52. -/
theorem star_60_52 (k : Class (Class α)) (b : Class α) :
    Included (Sum k) b↔Included k (Cl b) := by
  exact ⟨fun h a ha x hx=>h x ⟨a,ha,hx⟩,fun h x hx=>h hx.choose hx.choose_spec.1 x hx.choose_spec.2⟩
/-- ✱60·53. -/
theorem star_60_53 (k : Class (Class α)) (b : Class α) :
    Included b (Product k) ↔ ∀a,k a→Cl a b := by
  constructor
  · intro h a ha x hx; exact h x hx a ha
  · intro h x hx a ha; exact h a ha x hx
/-- ✱60·55. -/
theorem star_60_55 (a b : Class α) : Cl a=Cl b↔a=b := by
  constructor
  · intro h; apply ext; intro x; constructor
    · intro hx; have ha : Cl a a := fun _ h=>h; rw [h] at ha; exact ha x hx
    · intro hx; have hb : Cl b b := fun _ h=>h; rw [←h] at hb; exact hb x hx
  · rintro rfl; rfl
/-- ✱60·61. -/
theorem star_60_61 (a : Class α) :
    Included (fun b=>∃x,a x∧b=PM.Architecture.Star60Kernel.Singleton x) (ClEx a) := by rintro b ⟨x,hx,rfl⟩; exact star_60_57 a x hx
/-- ✱60·62. -/
theorem star_60_62 (a : Class α) (x y : α) :
    a x→a y→ClEx a (Union (PM.Architecture.Star60Kernel.Singleton x) (PM.Architecture.Star60Kernel.Singleton y)) := by
  intro hx hy; exact ⟨fun z h=>h.elim (fun e=>e ▸ hx) (fun e=>e ▸ hy),x,Or.inl rfl⟩
/-- ✱60·7, the class of subclasses is itself a class of classes. -/
theorem star_60_7 (a : Class α) : ∀b,Cl a b→∃c : Class α,b=c := fun b _=>⟨b,rfl⟩

end PM.Architecture.Star60MissingKernel
