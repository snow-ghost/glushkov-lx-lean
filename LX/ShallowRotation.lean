import LX.FiniteEnergyRotation
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem rotation_inversion_change (p : State (k+1)) :
    (inversionNumber (rotateConjugate p) : ℤ)-(inversionNumber p : ℤ)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by
  have hd := congrArg (fun v : ℕ => (v : ℤ)) (domain_rotation_inversions p)
  have hv := congrArg (fun v : ℕ => (v : ℤ)) (value_rotation_inversions (p*finRotate (k+1)))
  push_cast at hd hv
  simp only [← mul_assoc] at hv
  change (inversionNumber (rotateConjugate p) : ℤ)+2*((p*finRotate (k+1))⁻¹ 0 : ℤ)=
    (inversionNumber (p*finRotate (k+1)) : ℤ)+(k : ℤ) at hv
  have hb : ((p*finRotate (k+1))⁻¹ 0 : ℤ)=
      (p.symm 0 : ℤ)-1+(if p.symm 0=0 then (k+1 : ℤ) else 0) := by
    simpa only [mul_inv_rev,Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using inverse_rotate_int (p.symm 0)
  rw [hb] at hv
  by_cases hp : p 0=0
  · have hp' : p.symm 0=0 := by simpa only [hp] using p.symm_apply_apply 0
    simp only [hp',ite_true,Fin.val_zero,Nat.cast_zero] at hv
    simp only [hp,Fin.val_zero,Nat.cast_zero] at hd
    simp only [hp,ite_true]
    linarith only [hd,hv]
  · have hp' : p.symm 0 ≠ 0 := by
      intro h
      apply hp
      have he := congrArg p h
      simpa only [Equiv.apply_symm_apply] using he.symm
    simp only [hp',ite_false] at hv
    simp only [hp,ite_false]
    linarith only [hd,hv]

theorem rotation_energy_minus_inversions (p : State (k+1)) :
    (∑ i : Fin (k+1), |displacement (rotateConjugate p) i|)-
      (inversionNumber (rotateConjugate p) : ℤ)=
    (∑ i : Fin (k+1), |displacement p i|)-(inversionNumber p : ℤ) := by
  have hE := rotation_energy_change p
  have hI := rotation_inversion_change p
  linarith only [hE,hI]


#print axioms rotation_energy_minus_inversions
end LX.Core.FiniteCuts
