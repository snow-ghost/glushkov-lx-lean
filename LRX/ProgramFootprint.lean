import LRX.BufferFrame
import Mathlib

/-! A program using a set of buffer labels preserves every coordinate outside
that set, at all prefixes. This allows insertion of disjoint child cycles. -/
namespace LRX.BufferProgram
variable {n : ℕ}

def ProgramUses (S : Finset (Fin n)) (cs : List (Command n)) : Prop :=
  ∀ c ∈ cs, Uses S c


end LRX.BufferProgram
