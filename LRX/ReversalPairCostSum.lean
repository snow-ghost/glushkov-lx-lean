import LRX.ReversalPairDecomposition
import LRX.GapCostInversionDeficit

namespace LRX.FiniteCuts
open scoped BigOperators

theorem twice_sum_fin_values (k : ℕ) :
    2*(∑ i : Fin k, (i.val : ℤ))=(k : ℤ)*((k : ℤ)-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    push_cast
    nlinarith

theorem reversal_pair_rotation_sum (n : ℕ) :
    (∑ i : Fin (n/2), (2*(((reversalLeft i).rev : ℤ)-(reversalLeft i : ℤ))-2))=
      (n.choose 2 : ℤ)-(n/2 : ℕ) := by
  have hpoint (i : Fin (n/2)) :
      2*(((reversalLeft i).rev : ℤ)-(reversalLeft i : ℤ))-2=
        2*(n : ℤ)-4-4*(i.val : ℤ) := by
    have hi := i.isLt
    have hr : ((reversalLeft i).rev : ℤ)=(n : ℤ)-1-(i.val : ℤ) := by
      simp only [reversalLeft,Fin.val_rev]
      omega
    rw [hr]
    change 2*((n : ℤ)-1-(i.val : ℤ)-(i.val : ℤ))-2=_
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hs := twice_sum_fin_values (n/2)
  have hc := twice_choose_two_int n
  have hpar : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hpar with he | ho
  · have he' : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by exact_mod_cast he
    nlinarith
  · have ho' : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by exact_mod_cast ho
    nlinarith

#print axioms reversal_pair_rotation_sum
end LRX.FiniteCuts
