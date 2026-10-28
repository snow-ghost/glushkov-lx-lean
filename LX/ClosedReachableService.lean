import LX.PortRoute
import LX.RecenteredLift
import Mathlib

/-! At phase zero, the local target is conjugation by the cursor rotation.
This identity connects recentered lifts to literal permutation products. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_target_zero (p : State n) (r : Fin n) :
    localTarget p 0 r=(rotation r)⁻¹*p*rotation r := by
  change (rotation r)⁻¹*p*(rotation (0-r))⁻¹= _
  rw [rotation_sub]
  simp [rotation]

end LX.Core.RotationWords
