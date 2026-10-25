import LRX.PeriodicBuffer
import LRX.RecenteredLift
import Mathlib

/-! Reachable service at an arbitrary chosen port and final phase, with both
external cursor moves paid by actual words. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def portLoad (d : Fin n → ℤ) (r : Fin n) : ℤ :=
  ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ)
    ((i : ℤ)+localDisplacement d r i)


end LRX.RotationWords
