import LX.FiniteWindowInversions
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n k : ℕ}

def inversionOn (f : Fin k → Fin n) : ℕ :=
  ∑ i : Fin k, ∑ j : Fin k, if i.val < j.val ∧ (f j).val < (f i).val then 1 else 0

theorem inversion_on_first (f : Fin (k+1) → Fin n) :
    inversionOn f=inversionOn (fun i : Fin k => f i.succ)+
      ∑ i : Fin k, if (f i.succ).val < (f 0).val then 1 else 0 := by
  simp only [inversionOn,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    Nat.not_lt_zero,false_and,ite_false,Nat.zero_lt_succ,true_and,
    Nat.add_lt_add_iff_right,add_zero,zero_add]
  omega

theorem inversion_on_last (f : Fin (k+1) → Fin n) :
    inversionOn f=inversionOn (fun i : Fin k => f i.castSucc)+
      ∑ i : Fin k, if (f (Fin.last k)).val < (f i.castSucc).val then 1 else 0 := by
  have hlt (i : Fin k) : i.val < k := i.isLt
  have hnot (i : Fin k) : ¬k < i.val := by have := i.isLt; omega
  simp only [inversionOn,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,
    hlt,hnot,lt_self_iff_false,false_and,true_and,ite_false,Finset.sum_const_zero,
    add_zero,zero_add,Finset.sum_add_distrib]

theorem inversion_number_inverse (p : State n) : inversionNumber p⁻¹=inversionNumber p := by
  classical
  unfold inversionNumber
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        if (p i).val < (p j).val ∧ j.val < i.val then 1 else 0 := by
      rw [← Equiv.sum_comp p]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Equiv.sum_comp p]
      simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [and_comm]

#print axioms inversion_on_first
#print axioms inversion_on_last
#print axioms inversion_number_inverse
end LX.Core.FiniteCuts
