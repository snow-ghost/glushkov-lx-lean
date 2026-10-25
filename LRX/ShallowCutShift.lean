import LRX.FiniteEnergyRotation
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def Shallow (p : State n) : Prop :=
  (∑ i : Fin n, |displacement p.symm i|)=
    (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)+
      (p.support.card : ℤ)-1

def shiftConjugate (p : State n) (t : ℕ) : State n := (finRotate n^t)⁻¹*p*(finRotate n^t)


theorem shift_conjugate_succ (p : State n) (t : ℕ) :
    shiftConjugate p (t+1)=rotateConjugate (shiftConjugate p t) := by
  simp only [shiftConjugate,rotateConjugate,pow_succ,mul_inv_rev,mul_assoc]


theorem shift_conjugate_apply (p : State n) (c i : Fin n) :
    shiftConjugate p c.val i=p (i+c)-c := by
  have hP (j : Fin n) : (finRotate n^c.val) j=j+c := by
    simpa only [LRX.L,Fin.cast_val_eq_self] using AffineLift.rotation_power_apply c.val j
  have hR (j : Fin n) : (finRotate n^c.val)⁻¹ j=j-c := by
    apply (finRotate n^c.val).injective
    change (finRotate n^c.val) ((finRotate n^c.val).symm j)=(finRotate n^c.val) (j-c)
    rw [Equiv.apply_symm_apply,hP,sub_add_cancel]
  simp only [shiftConjugate,Equiv.Perm.mul_apply,hP,hR]


end LRX.FiniteCuts
