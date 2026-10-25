import LX.CompleteMapping
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]


theorem raw_offset_mass (p : State n) :
    (∑ i : Fin n,((p i-i : Fin n) : ℤ))=(n : ℤ)*(descendingPositions p).card := by
  have h := clockwise_representative_mass p
  simpa only [clockwise_difference_value] using h


end LX.AnchoredPhases
