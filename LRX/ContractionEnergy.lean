import LRX.ContractionInversions

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem succAbove_value (a : Fin (n+1)) (i : Fin n) :
    (a.succAbove i).val=if i.val < a.val then i.val else i.val+1 := by
  by_cases h : i.val < a.val
  · rw [if_pos h,Fin.succAbove_of_castSucc_lt a i h]
    rfl
  · rw [if_neg h,Fin.succAbove_of_le_castSucc a i (le_of_not_gt h)]
    rfl

/-- Deleting equal or consecutive row/column indices changes a surviving
entry's displacement by exactly its inversion incidence with the deleted entry. -/
theorem close_entry_energy (a b : Fin (n+1)) (hab : |(b : ℤ)-(a : ℤ)| ≤ 1) (i j : Fin n) :
    |(b.succAbove j : ℤ)-(a.succAbove i : ℤ)|=|(j : ℤ)-(i : ℤ)|+
      (if a.val < (a.succAbove i).val ∧ (b.succAbove j).val < b.val then (1 : ℤ) else 0)+
      (if (a.succAbove i).val < a.val ∧ b.val < (b.succAbove j).val then (1 : ℤ) else 0) := by
  simp only [abs_le] at hab
  change |((b.succAbove j).val : ℤ)-((a.succAbove i).val : ℤ)|=_
  simp only [succAbove_value]
  split_ifs <;> simp only [Nat.cast_add,Nat.cast_one,abs_eq_max_neg] <;> omega

theorem contraction_energy_price (p : State (n+1)) (a : Fin (n+1))
    (hadj : |displacement p a| ≤ 1) :
    (∑ i : Fin (n+1), |displacement p i|)=
      (∑ i : Fin n, |displacement (contract p a) i|)+|displacement p a|+
        (incidentInversions p a : ℤ) := by
  have hpoint (i : Fin n) : |displacement p (a.succAbove i)|=
      |displacement (contract p a) i|+
      (if a.val < (a.succAbove i).val ∧ (p (a.succAbove i)).val < (p a).val then (1 : ℤ) else 0)+
      (if (a.succAbove i).val < a.val ∧ (p a).val < (p (a.succAbove i)).val then (1 : ℤ) else 0) := by
    have h := close_entry_energy a (p a) hadj i (contract p a i)
    simpa only [contract_entry,displacement] using h
  have hm := Fin.sum_univ_succAbove (fun i => |displacement p i|) a
  simp_rw [hpoint] at hm
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hm
  have hr := Fin.sum_univ_succAbove
    (fun i : Fin (n+1) => if a.val < i.val ∧ (p i).val < (p a).val then (1 : ℤ) else 0) a
  have hc := Fin.sum_univ_succAbove
    (fun i : Fin (n+1) => if i.val < a.val ∧ (p a).val < (p i).val then (1 : ℤ) else 0) a
  simp only [lt_self_iff_false,false_and,ite_false,zero_add] at hr hc
  unfold incidentInversions
  push_cast
  rw [hr,hc]
  linarith only [hm]

theorem contraction_energy_minus_inversions (p : State (n+1)) (a : Fin (n+1))
    (hadj : |displacement p a| ≤ 1) :
    (∑ i : Fin n, |displacement (contract p a) i|)-(inversionNumber (contract p a) : ℤ)=
      (∑ i : Fin (n+1), |displacement p i|)-(inversionNumber p : ℤ)-|displacement p a| := by
  have hE := contraction_energy_price p a hadj
  have hI := congrArg (fun v : ℕ => (v : ℤ)) (contraction_inversion_price p a)
  push_cast at hI
  linarith only [hE,hI]

#print axioms contraction_energy_price
#print axioms contraction_energy_minus_inversions
end LRX.FiniteCuts
