import LRX.BufferProgram
import Mathlib

/-! Initial and final contracts for the periodic buffer compiler. Reconstruction
is over integers, so a closed physical service cannot silently discard winding. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open BufferMachine
variable {n : ℕ} [NeZero n]

def initialLogical : Logical n :=
  ⟨0, fun i => PeriodicBuffer.contract (n : ℤ) (i : ℤ), 0⟩



end LRX.BufferProgram
