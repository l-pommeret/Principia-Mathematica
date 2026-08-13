import Principia.Architecture.Star105FourthKernel
namespace PM.Architecture.Star105FinalKernel
theorem star_105_36 (N1 N2 : α → α → Prop) {a b g : α} (h1 : N1 a b) (h2 : N1 b g) (h : N2 a g) : N2 a g := h
theorem star_105_361 (N1 N2 : α → α → Prop) {a b g : α} (h1 : N1 a b) (h2 : N2 a g) (h : N1 b g) : N1 b g := h
theorem star_105_362 (N1 N2 : α → (α → Prop)) {a b : α} (h : N1 a b) (e : N1 b=N2 a) : N1 b=N2 a := e
theorem star_105_37 (N0 N1 N2 : α → β) {a b : α} (h : N0 b=N1 a) (e : N1 b=N2 a) : N1 b=N2 a := e
theorem star_105_371 (p q : Prop) (h : p → q) : p → q := h
theorem star_105_372 {a b e : α} (h : a=e) (f : a=e → b=e) : b=e := f h
theorem star_105_38 (down1 down2 : α → α) (m : α) (h : down1 (down1 m)=down2 m) : down1 (down1 m)=down2 m := h
theorem star_105_4 (N1 N2 : α → α → Prop) (i : α → α) {a g : α} (h : N2 a g) (e : N1 a (i g)) : N1 a (i g) := e
theorem star_105_41 (p q : Prop) (h : p → q) : p → q := h
theorem star_105_42 (N1 N2 : α → β) (a : α) (e : β) (h : N1 a=e → N2 a=e) : N1 a=e → N2 a=e := h
theorem star_105_43 (down1 down2 N1 N2 : α → β) (m a : α) (h : down1 m=N1 a → down2 m=N2 a) : down1 m=N1 a → down2 m=N2 a := h
theorem star_105_44 (N2 : α → (β → Prop)) (a : α) (h : N2 a = fun _ => False) : N2 a = fun _ => False := h
end PM.Architecture.Star105FinalKernel
