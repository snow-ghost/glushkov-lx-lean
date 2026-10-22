import LRX.FiniteInversionRotation

namespace LRX.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

def rotateConjugate {n : ℕ} (p : State n) : State n := (finRotate n)⁻¹*p*finRotate n

theorem inverse_rotate_int (i : Fin (k+1)) :
    ((finRotate (k+1)).symm i : ℤ)=(i : ℤ)-1+(if i=0 then (k+1 : ℤ) else 0) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : (finRotate (k+1)).symm 0=Fin.last k := by
      apply (finRotate (k+1)).injective
      simp only [Equiv.apply_symm_apply,finRotate_last]
    rw [hz]
    simp
  · have hs : (finRotate (k+1)).symm j.succ=j.castSucc := by
      apply (finRotate (k+1)).injective
      simp only [Equiv.apply_symm_apply,rotate_castSucc]
    rw [hs]
    simp

theorem rotation_energy_point (p : State (k+1)) (hp : p 0 ≠ 0) (i : Fin (k+1)) :
    |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)|=
      |displacement p i|+
      (if i=0 then (k+1 : ℤ)-2*(p 0 : ℤ) else 0)+
      (if i=p.symm 0 then (k+1 : ℤ)-2*(p.symm 0 : ℤ) else 0) := by
  have hb : p.symm 0 ≠ 0 := by
    intro h
    apply hp
    have he := congrArg p h
    simpa only [Equiv.apply_symm_apply] using he.symm
  have hz : p i=0 ↔ i=p.symm 0 := by
    constructor
    · intro h
      exact (p.symm_apply_apply i).symm.trans (congrArg p.symm h)
    · intro h
      rw [h,p.apply_symm_apply]
  rw [inverse_rotate_int,inverse_rotate_int]
  unfold displacement
  by_cases hi : i=0
  · subst i
    have ha0 : (0 : ℤ) ≤ p 0 := by positivity
    have han : (p 0 : ℤ) < k+1 := by exact_mod_cast (p 0).isLt
    simp only [hp,hb,Ne.symm hb,ite_false,ite_true,Fin.val_zero,Nat.cast_zero]
    rw [abs_of_nonpos (show (p 0 : ℤ)-1+0-(0-1+(k+1 : ℤ)) ≤ 0 by omega),
      abs_of_nonneg (show (0 : ℤ) ≤ (p 0 : ℤ)-0 by omega)]
    omega
  · by_cases hib : i=p.symm 0
    · subst i
      have hb0 : (0 : ℤ) ≤ p.symm 0 := by positivity
      have hbn : (p.symm 0 : ℤ) < k+1 := by exact_mod_cast (p.symm 0).isLt
      simp only [p.apply_symm_apply,hb,ite_false,ite_true,Fin.val_zero,Nat.cast_zero]
      rw [abs_of_nonneg (show (0 : ℤ) ≤ 0-1+(k+1 : ℤ)-((p.symm 0 : ℤ)-1+0) by omega),
        abs_of_nonpos (show (0 : ℤ)-(p.symm 0 : ℤ) ≤ 0 by omega)]
      omega
    · have hpi : p i ≠ 0 := fun h => hib (hz.mp h)
      simp only [hi,hib,hpi,ite_false,add_zero]
      congr 1
      ring

theorem rotation_energy_change (p : State (k+1)) :
    (∑ i : Fin (k+1), |displacement (rotateConjugate p) i|)-
      (∑ i : Fin (k+1), |displacement p i|)=
      if p 0=0 then 0 else 2*(k+1 : ℤ)-2*(p 0 : ℤ)-2*(p.symm 0 : ℤ) := by
  classical
  have hm : (∑ i : Fin (k+1), |displacement (rotateConjugate p) i|)=
      ∑ i : Fin (k+1), |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)| := by
    have h := Equiv.sum_comp (finRotate (k+1)).symm (fun i : Fin (k+1) => |displacement (rotateConjugate p) i|)
    simpa only [displacement,rotateConjugate,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      Equiv.apply_symm_apply] using h.symm
  rw [hm]
  by_cases hp : p 0=0
  · have hz (i : Fin (k+1)) : p i=0 ↔ i=0 := by
      calc
        p i=0 ↔ p i=p 0 := by rw [hp]
        _ ↔ i=0 := p.injective.eq_iff
    have he (i : Fin (k+1)) :
        |((finRotate (k+1)).symm (p i) : ℤ)-((finRotate (k+1)).symm i : ℤ)|=|displacement p i| := by
      rw [inverse_rotate_int,inverse_rotate_int]
      simp only [hz]
      unfold displacement
      congr 1
      ring
    simp only [he,hp,ite_true,sub_self]
  · simp only [hp,ite_false]
    simp_rw [rotation_energy_point p hp]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp
    ring

#print axioms rotation_energy_change
end LRX.FiniteCuts
