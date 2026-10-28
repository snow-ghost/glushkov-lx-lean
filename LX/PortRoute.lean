import LX.LiftedModel
import LX.RotationWords
import Mathlib

/-! Rotations indexed by a finite cursor and their algebraic identities.
Addition and subtraction of cursors agree with permutation multiplication. -/
namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def rotation (r : Fin n) : State n := L n^r.val

theorem rotation_add (a b : Fin n) : rotation (a+b)=rotation a*rotation b := by
  apply Equiv.ext
  intro i
  simp only [rotation, AffineLift.rotation_power_apply, Fin.cast_val_eq_self, Equiv.Perm.mul_apply]
  abel

theorem rotation_sub (a b : Fin n) : rotation (b-a)=(rotation a)⁻¹*rotation b := by
  have h : rotation a*rotation (b-a)=rotation b := by
    rw [← rotation_add]
    congr 1
    abel
  calc
    rotation (b-a)=(rotation a)⁻¹*(rotation a*rotation (b-a)) := by group
    _ = _ := by rw [h]


end LX.Core.RotationWords
