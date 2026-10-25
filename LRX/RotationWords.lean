import LRX.ZeroLift
import Mathlib

/-! Paid signed rotations and shortest cyclic offsets. No change of cursor is
introduced without an explicit L/R word and its length. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def spin : ℤ → List Letter
  | .ofNat k => List.replicate k .l
  | .negSucc k => List.replicate (k+1) .r





def shortOffset (c : Fin n) : ℤ := if 2*c.val ≤ n then (c : ℤ) else (c : ℤ)-(n : ℤ)

def toPort (c : Fin n) : List Letter := spin (shortOffset c)

theorem rotation_period : L n ^ n=1 := by
  apply Equiv.ext
  intro i
  simp [AffineLift.rotation_power_apply]





end LRX.RotationWords
