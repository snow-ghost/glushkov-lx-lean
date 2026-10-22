import LRX.WindowReplacementInversions
import LRX.FiniteInversionDecomposition

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem ordered_pair_sum (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i.val<j.val then (1 : ℕ) else 0)=n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Nat.not_lt_zero,
      ite_false,Nat.zero_lt_succ,ite_true,Nat.add_lt_add_iff_right,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,zero_add]
    rw [ih,Nat.choose_succ_succ,Nat.choose_one_right]

/-- Reversal attains the full finite inversion capacity, including the empty window. -/
theorem inversion_number_reversal (n : ℕ) : inversionNumber (Fin.revPerm : State n)=n.choose 2 := by
  have hpoint (i j : Fin n) :
      (if i.val<j.val ∧ ((Fin.revPerm : State n) j).val<((Fin.revPerm : State n) i).val then (1 : ℕ) else 0)=
      if i.val<j.val then 1 else 0 := by
    have hi := i.isLt
    have hj := j.isLt
    change (if i.val<j.val ∧ j.rev.val < i.rev.val then (1 : ℕ) else 0)=_
    simp only [Fin.val_rev]
    split_ifs <;> omega
  simp only [inversionNumber,hpoint,ordered_pair_sum]

/-- Reversal realizes the largest cut load at every position. -/
theorem reversal_half_load (n e : ℕ) (he : e ≤ n) :
    halfLoad (Fin.revPerm : State n) e=min e (n-e) := by
  have hf : forward (Fin.revPerm : State n) e=
      Finset.univ.filter (fun i : Fin n => i.val < min e (n-e)) := by
    ext i
    simp only [mem_forward,Finset.mem_filter,Finset.mem_univ,true_and]
    change (i.val<e ∧ e ≤ i.rev.val) ↔ _
    simp only [Fin.val_rev]
    have hi := i.isLt
    omega
  unfold halfLoad
  rw [hf,Fin.card_filter_val_lt]
  omega

theorem half_load_le_reversal (p : State n) (e : ℕ) :
    halfLoad p e ≤ halfLoad (Fin.revPerm : State n) e := by
  by_cases he : e ≤ n
  · rw [reversal_half_load n e he]
    exact half_load_capacity p e he
  · have hz : forward p e=∅ := by
      ext i
      simp only [mem_forward,Finset.notMem_empty,iff_false,not_and]
      intro hi
      have hp := (p i).isLt
      omega
    simp [halfLoad,hz]

#print axioms inversion_number_reversal
#print axioms half_load_le_reversal
end LRX.FiniteCuts
