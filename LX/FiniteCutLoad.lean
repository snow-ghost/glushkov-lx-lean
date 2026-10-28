import LX.Graph
import Mathlib

import LX.PeriodicBuffer
import LX.RecenteredLift


/-! Displacements of finite permutations define balanced affine lifts.
The canonical finite lift has phase zero. -/
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

def displacement (p : State b) (i : Fin b) : ℤ := (p i : ℤ)-(i : ℤ)

theorem canonical_lift (p : State b) : AffineLift.IsLift p.symm 0 (displacement p) := by
  unfold displacement
  simpa only [Equiv.symm_symm] using AffineLift.canonical_lift p.symm

#print axioms canonical_lift
end LX.Core.FiniteCuts
