import LX.FiniteEnergyRotation
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def shiftConjugate (p : State n) (t : ℕ) : State n := (finRotate n^t)⁻¹*p*(finRotate n^t)


theorem shift_conjugate_succ (p : State n) (t : ℕ) :
    shiftConjugate p (t+1)=rotateConjugate (shiftConjugate p t) := by
  simp only [shiftConjugate,rotateConjugate,pow_succ,mul_inv_rev,mul_assoc]


theorem shift_conjugate_apply (p : State n) (c i : Fin n) :
    shiftConjugate p c.val i=p (i+c)-c := by
  have hP (j : Fin n) : (finRotate n^c.val) j=j+c := by
    simpa only [LX.Core.L,Fin.cast_val_eq_self] using AffineLift.rotation_power_apply c.val j
  have hR (j : Fin n) : (finRotate n^c.val)⁻¹ j=j-c := by
    apply (finRotate n^c.val).injective
    change (finRotate n^c.val) ((finRotate n^c.val).symm j)=(finRotate n^c.val) (j-c)
    rw [Equiv.apply_symm_apply,hP,sub_add_cancel]
  simp only [shiftConjugate,Equiv.Perm.mul_apply,hP,hR]


end LX.Core.FiniteCuts
