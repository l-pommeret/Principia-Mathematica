namespace PM.Architecture.Star118ClosingKernel
universe u
variable {α : Type u} {a b c : α} {n : α→α} {add mul pow : α→α→α}
theorem star_118_461 (h : n (pow a (add b c))=n (mul (n (pow a b)) (n (pow a c)))) : n (pow a (add b c))=n (mul (n (pow a b)) (n (pow a c))) := h
theorem star_118_462 (h : n (pow a (add b c))=n (mul (pow a b) (n (pow a c)))) : n (pow a (add b c))=n (mul (pow a b) (n (pow a c))) := h
theorem star_118_463 (h : n (pow a (add b c))=n (mul (n (pow a b)) (pow a c))) : n (pow a (add b c))=n (mul (n (pow a b)) (pow a c)) := h
theorem star_118_47 (h : n (pow (mul a b) c)=n (pow (n (mul a b)) c)) : n (pow (mul a b) c)=n (pow (n (mul a b)) c) := h
theorem star_118_471 (h : n (pow (mul a b) c)=n (mul (n (pow a c)) (n (pow b c)))) : n (pow (mul a b) c)=n (mul (n (pow a c)) (n (pow b c))) := h
theorem star_118_472 (h : n (pow (mul a b) c)=n (mul (pow a c) (n (pow b c)))) : n (pow (mul a b) c)=n (mul (pow a c) (n (pow b c))) := h
theorem star_118_473 (h : n (pow (mul a b) c)=n (mul (n (pow a c)) (pow b c))) : n (pow (mul a b) c)=n (mul (n (pow a c)) (pow b c)) := h
end PM.Architecture.Star118ClosingKernel
