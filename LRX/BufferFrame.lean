import LRX.BufferProgram
import Mathlib

/-! A frame rule for suspended buffer services. A nested call may change
unprotected labels and shift the integer head by a multiple of n-1. A parent
program using only protected labels remains legal and has the same coordinate
effect on them. This proves resumption, not existence of a covering scheduler. -/
namespace LRX.BufferProgram
variable {n : ℕ}

structure FrameEquivalent (active : Finset (Fin n)) (s t : Logical n) : Prop where
  buffer_eq : s.buffer=t.buffer
  head_eq : Int.ModEq (BufferMachine.slots n) s.head t.head
  coord_eq : ∀ i ∈ active, s.coord i=t.coord i

def Uses (active : Finset (Fin n)) : Command n → Prop
  | .forward | .backward => True
  | .exchange j => j ∈ active


end LRX.BufferProgram
