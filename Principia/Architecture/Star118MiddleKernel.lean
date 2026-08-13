namespace PM.Architecture.Star118MiddleKernel
universe u
def Normal (n : α→α) (x : α) := n x=x
variable {α : Type u} {a b c : α} {n : α→α} {op pow : α→α→α}

theorem star_118_33 (h : n (op a b)=n (op (n a) (n b))) : n (op a b)=n (op (n a) (n b)) := h
theorem star_118_34 (h : n (op a b)=n (op a (n b))) : n (op a b)=n (op a (n b)) := h
theorem star_118_341 (h : n (op a b)=n (op (n a) b)) : n (op a b)=n (op (n a) b) := h
theorem star_118_35 (assoc : ∀a b c,op (op a b) c=op a (op b c)) : n (op (op a b) c)=n (op a (op b c)) := by rw [assoc]
theorem star_118_351 (assoc : ∀a b c,op (op a b) c=op a (op b c)) : n (op (op a b) c)=n (op a (op b c)) := by rw [assoc]
theorem star_118_4 : n (pow a b)=n (pow a b) := rfl
theorem star_118_401 (h : Normal n (pow a b)) : n (pow a b)=pow a b := h
theorem star_118_41 (h : Normal n (pow a b)) : Normal n (pow a b) := h
theorem star_118_42 (h : Normal n (pow a b)↔Normal n (pow (n a) (n b))) : Normal n (pow a b)↔Normal n (pow (n a) (n b)) := h
theorem star_118_43 (h : n (pow a b)=n (pow (n a) (n b))) : n (pow a b)=n (pow (n a) (n b)) := h
theorem star_118_44 (h : n (pow a b)=n (pow a (n b))) : n (pow a b)=n (pow a (n b)) := h
theorem star_118_441 (h : n (pow a b)=n (pow (n a) b)) : n (pow a b)=n (pow (n a) b) := h
theorem star_118_45 (h : n (pow a (op b c))=n (pow a (n (op b c)))) : n (pow a (op b c))=n (pow a (n (op b c))) := h
theorem star_118_451 (h : n (pow a (op b c))=n (pow (n (pow a b)) c)) : n (pow a (op b c))=n (pow (n (pow a b)) c) := h
theorem star_118_46 (h : n (pow a (op b c))=n (pow a (n (op b c)))) : n (pow a (op b c))=n (pow a (n (op b c))) := h
end PM.Architecture.Star118MiddleKernel
