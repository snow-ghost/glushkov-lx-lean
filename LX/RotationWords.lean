import LX.ZeroLift
import Mathlib

/-! The cyclic generator has period `n`.
This identity allows inverse rotations to be expanded into forward words. -/
namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_period : L n ^ n=1 := by
  apply Equiv.ext
  intro i
  simp [AffineLift.rotation_power_apply]


end LX.Core.RotationWords
