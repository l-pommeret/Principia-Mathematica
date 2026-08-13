namespace PM.Architecture.Star126CardinalArchitecture

/-- The finite (inductive) cardinal numbers, represented canonically. -/
abbrev FiniteCardinal := Nat
def NCind (_ : FiniteCardinal) : Prop := True
def NonzeroNCind (n : FiniteCardinal) := NCind n ∧ n ≠ 0
def successor (n : FiniteCardinal) := n + 1
def cadd := Nat.add
def cmul := Nat.mul
def cpow := Nat.pow

theorem ncind_successor : NCind n → NCind (successor n) := fun _ => trivial
theorem ncind_add : NCind m → NCind n → NCind (cadd m n) := fun _ _ => trivial
theorem ncind_mul : NCind m → NCind n → NCind (cmul m n) := fun _ _ => trivial
theorem ncind_pow : NCind m → NCind n → NCind (cpow m n) := fun _ _ => trivial

end PM.Architecture.Star126CardinalArchitecture
