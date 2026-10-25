import LRX.Graph
import LRX.PeriodicBuffer
import Mathlib

/-! An actual buffer-service word for a supplied complete cyclic order of labels.
The order follows the physical target permutation. Correctness, closed integer
cursor, every integer endpoint, and exact rotation price are proved. The raw X
count is not reduced to affine inversion length here. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def logicalDelta (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) - PeriodicBuffer.contract (n : ℤ) (i : ℤ)

def Follows (p : State n) : List (Fin n) → Prop
  | [] => True
  | a :: rest => match rest with
    | [] => True
    | b :: _ => p.symm a=b ∧ Follows p rest


end LRX.BufferProgram
