import LRX.BufferProgram
import Mathlib

/-! Visited head classes are preserved by insertion of a disjoint child call.
Both endpoints of every program are included in the visit predicate. -/
namespace LRX.BufferProgram
variable {n : ℕ}

def Visits : List (Command n) → Logical n → ℤ → Prop
  | [], t, y => Int.ModEq (BufferMachine.slots n) t.head y
  | c::cs, t, y => Int.ModEq (BufferMachine.slots n) t.head y ∨ Visits cs (logicalStep c t) y


end LRX.BufferProgram
