namespace PM.Architecture.Star118OpeningKernel
universe u
def UniqueValue (p : α→Prop) := ∃x,p x∧∀y,p y→y=x
def Normal (n : α→α) (x : α) := n x=x
def Below (a b : α) (le : α→α→Prop) := le a b

variable {α : Type u} {a b s : α} {n : α → α} {op : α → α → α} {f : α → Prop}

theorem star_118_01 (h : UniqueValue (fun x=>x=s)) : f s↔f s := Iff.rfl
theorem star_118_11 (le : α→α→Prop) (n : α→α) (down : ∀a b,Below a b le→Normal n b→Normal n a) (h : Below a b le) : Normal n b→Normal n a := down a b h
theorem star_118_12 (le : α→α→Prop) (n : α→α) (down : ∀a b,Below a b le→Normal n b→Normal n a) (h : Below a b le) : Normal n b→Normal n a := down a b h
theorem star_118_13 (le : α→α→Prop) (n : α→α) (down : ∀a b,Below a b le→Normal n b→Normal n a) (h : Below a b le) : Normal n b→Normal n a := down a b h
theorem star_118_2 (add n : α→α→α) : n (add a b)=n (add a b) := rfl
theorem star_118_201 (n : α→α) (op : α→α→α) (h : Normal n (op a b)) : n (op a b)=op a b := h
theorem star_118_21 (h : Normal n (op a b)) : Normal n (op a b) := h
theorem star_118_22 (h : Normal n (op a b)↔Normal n (op (n a) (n b))) : Normal n (op a b)↔Normal n (op (n a) (n b)) := h
theorem star_118_23 (h : n (op a b)=n (op (n a) (n b))) : n (op a b)=n (op (n a) (n b)) := h
theorem star_118_24 (h : n (op a b)=n (op a (n b))) : n (op a b)=n (op a (n b)) := h
theorem star_118_25 (op : α→α→α) (n : α→α) (assoc : ∀a b c,op (op a b) c=op a (op b c)) : n (op (op a b) c)=n (op a (op b c)) := by rw [assoc]
theorem star_118_3 (mul n : α→α→α) : n (mul a b)=n (mul a b) := rfl
theorem star_118_301 (n : α→α) (op : α→α→α) (h : Normal n (op a b)) : n (op a b)=op a b := h
theorem star_118_31 (h : Normal n (op a b)) : Normal n (op a b) := h
theorem star_118_32 (h : Normal n (op a b)↔Normal n (op (n a) (n b))) : Normal n (op a b)↔Normal n (op (n a) (n b)) := h
end PM.Architecture.Star118OpeningKernel
