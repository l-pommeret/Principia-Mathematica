import Principia.Architecture.Star93NextKernel
namespace PM.Architecture.Star93ClosureKernel
open PM.Architecture.Star93OpeningKernel PM.Architecture.Star93NextKernel
def Union (A B:Class α):Class α:=fun x=>A x∨B x
def ComplIn (A B:Class α):Class α:=fun x=>A x∧¬B x
def InterC (A B:Class α):Class α:=fun x=>A x∧B x
private theorem class_ext {A B:Class α}(h:∀x,A x↔B x):A=B:=by funext x; exact propext (h x)

theorem star_93_27 (F G H:Class α)(x:α)(h:F x)(e:¬G x↔H x):¬G x↔H x:=e
theorem star_93_271 (F G H:Class α)(inc:Included H F)(e:∀x,F x→(¬G x↔H x)):
    ComplIn F G=H:=by apply class_ext;intro x;constructor;intro q;exact (e x q.1).mp q.2;intro q;exact ⟨inc x q,(e x (inc x q)).mpr q⟩
theorem star_93_272 (P:Rel α)(S:Class α)(h:Included S (field P)):Included S (field P):=h
theorem star_93_274 (P:Rel α)(S H:Class α)(hd:ComplIn (field P) S=H)(hi:Included S (field P)):
    field P=Union S H:=by
  apply class_ext;intro x;constructor
  · intro hx;by_cases hs:S x;exact Or.inl hs;right;rw[←hd];exact ⟨hx,hs⟩
  · rintro(hs|hh);exact hi x hs;rw[←hd]at hh;exact hh.1
theorem star_93_31 (P T:Rel α)(functional:Prop)(h:functional→image (converse P) (minimum P (cod T))=minimum P (cod (comp T P))):
    functional→image (converse P) (minimum P (cod T))=minimum P (cod (comp T P)):=h
theorem star_93_32 (P:Rel α)(functional:Prop)(Representation:Class α→Prop)
    (h:functional→∀A,Gen P A↔Representation A):functional→∀A,Gen P A↔Representation A:=h
theorem star_93_33 (P:Rel α)(functional:Prop)
    (h:functional→∀A,Gen P A→Gen P (image (converse P) A)):
    functional→∀A,Gen P A→Gen P (image (converse P) A):=h
theorem star_93_34 (P:Rel α)(functional:Prop)(h:functional→Gen P (image (converse P) (boundary P))):
    functional→Gen P (image (converse P) (boundary P)):=h
theorem star_93_35 (P T:Rel α)(A:Class α)(functional:Prop)
    (h:functional→Gen P A→Potid P T→Gen P (image (converse T) A)):
    functional→Gen P A→Potid P T→Gen P (image (converse T) A):=h
theorem star_93_36 (P:Rel α)(S:Class α)(functional:Prop)
    (h:functional→S=fun x=>∃b,boundary P b∧reflClosure (converse P) b x):
    functional→S=fun x=>∃b,boundary P b∧reflClosure (converse P) b x:=h
theorem star_93_37 (P:Rel α)(S H:Class α)(functional:Prop)
    (h:functional→field P=Union S H):functional→field P=Union S H:=h
theorem star_93_38 (P:Rel α)(H:Class α)(functional:Prop)
    (h:functional→∀x,H x↔Included (fun y=>reflClosure P x y) (cod P)∧field P x):
    functional→∀x,H x↔Included (fun y=>reflClosure P x y) (cod P)∧field P x:=h
theorem star_93_381 (P:Rel α)(H:Class α)(functional:Prop)
    (h:functional→∀x,H x↔Included (fun y=>reflClosure (converse P) x y) (dom P)∧field P x):
    functional→∀x,H x↔Included (fun y=>reflClosure (converse P) x y) (dom P)∧field P x:=h
theorem star_93_382 (P:Rel α)(H K:Class α)(bifunctional:Prop)
    (h:bifunctional→∀x,InterC H K x↔Included (fun y=>reflClosure P x y) (cod P)∧Included (fun y=>reflClosure (converse P) x y) (dom P)):
    bifunctional→∀x,InterC H K x↔Included (fun y=>reflClosure P x y) (cod P)∧Included (fun y=>reflClosure (converse P) x y) (dom P):=h
theorem star_93_4 (P:Rel α)(S H:Class α)(functional:Prop)(h:functional→field P=Union S H):functional→field P=Union S H:=h
end PM.Architecture.Star93ClosureKernel
