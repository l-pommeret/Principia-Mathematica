import Principia.Deduction.Star9Derived

namespace PM.RamifiedSyntax

example (n : Nat) : max 0 n = n := by rfl
example (n : Nat) : max n 0 = n := by rfl

end PM.RamifiedSyntax
