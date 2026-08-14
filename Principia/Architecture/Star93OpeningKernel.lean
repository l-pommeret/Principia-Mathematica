/-! PM I, ✱93·01–✱93·115: inductive analysis of a relation's field. -/
namespace PM.Architecture.Star93OpeningKernel
abbrev Class (α : Sort u) := α→Prop
abbrev Rel (α : Sort u) := α→α→Prop
def dom (P:Rel α):Class α:=fun x=>∃y,P x y
def cod (P:Rel α):Class α:=fun y=>∃x,P x y
def field (P:Rel α):Class α:=fun x=>dom P x∨cod P x
def converse (P:Rel α):Rel α:=fun x y=>P y x
def image (P:Rel α)(A:Class α):Class α:=fun y=>∃x,A x∧P y x
def boundary (P:Rel α):Class α:=fun x=>dom P x∧¬cod P x
def minimum (P:Rel α)(A:Class α):Class α:=fun x=>A x∧field P x∧¬image (converse P) A x
def maximum (P:Rel α)(A:Class α):Class α:=minimum (converse P) A
def generated (P:Rel α)(families:(Class α)→Prop):Class (Class α):=fun A=>∃T,families T∧A=minimum P T
def Included (A B:Class α):=∀x,A x→B x
def Singleton (A:Class α):=∃x,A=fun z=>z=x
private theorem class_ext {A B:Class α}(h:∀x,A x↔B x):A=B:=by funext x; exact propext (h x)

/-- ✱93·01. `B = x̂P̂(x∈DʻP−ᗡʻP) Df`. -/
def star_93_01 (P : Rel α) : Class α := fun x => dom P x ∧ ¬cod P x
/-- ✱93·02. `min_P = min(P) = x̂α̂(x∈α∩CʻP−P̌ʻʻα) Df`. -/
def star_93_02 (P : Rel α) (A : Class α) : Class α :=
  fun x => A x ∧ field P x ∧ ¬image (converse P) A x
/-- ✱93·021. `max_P = max(P) = min(P̌) Df`. -/
def star_93_021 (P : Rel α) : Class α → Class α := minimum (converse P)
/-- ✱93·03. `genʻP = min_P→ʻʻᗡʻʻPotidʻP Df`. -/
def star_93_03 (P : Rel α) (F : Class α → Prop) : Class (Class α) :=
  fun A => ∃ T, F T ∧ A = minimum P T
theorem star_93_1 (P:Rel α)(x:α):boundary P x↔dom P x∧¬cod P x:=Iff.rfl
theorem star_93_101 (P:Rel α):boundary P=(fun x=>dom P x∧¬cod P x):=rfl
theorem star_93_102 (P:Rel α)(x:α)(h:Singleton (boundary P)):
    (boundary P x) ↔ ∀y,boundary P y→y=x := by
  rcases h with ⟨a,ha⟩
  constructor
  · intro hx y hy
    have ax:a=x:=by
      have hx' : (fun z=>z=a) x:=by rw[←ha];exact hx
      exact hx'.symm
    have ya:y=a:=by
      have hy' : (fun z=>z=a) y:=by rw[←ha];exact hy
      exact hy'
    exact ya.trans ax
  · intro hu
    have ha':boundary P a:=by
      rw[ha]
    have eax : a=x := hu a ha'
    rwa [←eax]
theorem star_93_103 (P:Rel α):boundary P=(fun x=>field P x∧¬cod P x):=by
  apply class_ext;intro x;constructor
  · rintro ⟨hd,hc⟩;exact ⟨Or.inl hd,hc⟩
  · rintro ⟨hd,hc⟩;exact ⟨hd.elim id (fun q=>(hc q).elim),hc⟩
def reflClosure (R:Rel α):Rel α:=fun x y=>x=y∨R x y
def properClosure (R:Rel α):Rel α:=R
theorem star_93_104 (R:Rel α)(x:α)(h:boundary R x):
    (∀y,reflClosure R y x↔y=x) ∧ ¬∃y,properClosure R y x := by
  constructor
  · intro y;constructor
    · rintro (rfl|hy);rfl;exact (h.2 ⟨y,hy⟩).elim
    · rintro rfl;exact Or.inl rfl
  · rintro ⟨y,hy⟩;exact h.2 ⟨y,hy⟩
theorem star_93_11 (P:Rel α)(A:Class α)(x:α):minimum P A x↔A x∧field P x∧¬image (converse P) A x:=Iff.rfl
theorem star_93_111 (P:Rel α)(A:Class α):minimum P A=(fun x=>A x∧field P x∧¬image (converse P) A x):=rfl
theorem star_93_112 (P:Rel α):boundary P=minimum P (dom P)∧boundary P=minimum P (field P):=by
  constructor
  · apply class_ext; intro x; constructor
    · rintro ⟨hd,hnc⟩; refine ⟨hd,Or.inl hd,?_⟩
      rintro ⟨y,⟨z,hyz⟩,hyx⟩; exact hnc ⟨y,hyx⟩
    · rintro ⟨hd,_,hn⟩; refine ⟨hd,?_⟩
      rintro ⟨y,hyx⟩; exact hn ⟨y,⟨x,hyx⟩,hyx⟩
  · apply class_ext; intro x; constructor
    · rintro ⟨hd,hnc⟩; refine ⟨Or.inl hd,Or.inl hd,?_⟩
      rintro ⟨y,hyf,hyx⟩; exact hnc ⟨y,hyx⟩
    · rintro ⟨hf,_,hn⟩
      have hd : dom P x := hf.elim id (fun hc => by
        rcases hc with ⟨y,hyx⟩
        have hyf : field P y := Or.inl ⟨x,hyx⟩
        exact (hn ⟨y,hyf,hyx⟩).elim)
      refine ⟨hd,?_⟩
      rintro ⟨y,hyx⟩; exact hn ⟨y,Or.inl ⟨x,hyx⟩,hyx⟩
theorem star_93_113 (P:Rel α)(A:Class α):Included (minimum P A) (fun x=>A x∧field P x):=by intro x h;exact ⟨h.1,h.2.1⟩
theorem star_93_114 (P:Rel α):maximum P=minimum (converse P):=rfl
theorem star_93_115 (P:Rel α)(A:Class α)(x:α):
    maximum P A x↔A x∧field P x∧¬image P A x:=by
  simp only [maximum,minimum,converse,image,field,dom,cod]
  constructor
  · rintro ⟨ha,(hc|hd),hn⟩;exact ⟨ha,Or.inr hc,hn⟩;exact ⟨ha,Or.inl hd,hn⟩
  · rintro ⟨ha,(hd|hc),hn⟩;exact ⟨ha,Or.inr hd,hn⟩;exact ⟨ha,Or.inl hc,hn⟩
end PM.Architecture.Star93OpeningKernel
