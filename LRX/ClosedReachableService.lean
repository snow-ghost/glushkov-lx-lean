import LRX.PortRoute
import LRX.RecenteredLift
import Mathlib

/-! Closed route tasks are supplied by the proved lifted service construction.
Their contracts do not require a separately assumed word or execution witness. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_target_zero (p : State n) (r : Fin n) :
    localTarget p 0 r=(rotation r)⁻¹*p*rotation r := by
  change (rotation r)⁻¹*p*(rotation (0-r))⁻¹= _
  rw [rotation_sub]
  simp [rotation]

def idleService (r : Fin n) : ClosedService n where
  port := r
  word := []
  target := 1
  correct := by simp
  closed := rfl


end LRX.RotationWords
