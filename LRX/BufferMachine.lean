import LRX.LiftedModel
import LRX.PeriodicBuffer
import Mathlib

/-! Exact periodic buffer macros connected to the literal lifted LRX executor.
The buffer identity, integer logical positions and integer head are retained. -/
namespace LRX.BufferMachine
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LiftedModel

abbrev slots (n : ℕ) : ℤ := (n : ℤ)-1

variable {n : ℕ} [NeZero n]

structure Represents (s : Configuration n) (b : Fin n) (y : Fin n → ℤ) : Prop where
  aligned : Aligned s
  head : (y b-s.cursor) % slots n = 0
  positions : ∀ i, s.position i = if i=b then PeriodicBuffer.buffer (slots n) s.cursor (y i)
    else PeriodicBuffer.passive (slots n) s.cursor (y i)


def forward (s : Configuration n) : Configuration n := run [.x,.l] s

def backward (s : Configuration n) : Configuration n := run [.r,.x] s

def exchange (s : Configuration n) : Configuration n := step .x s


end LRX.BufferMachine
