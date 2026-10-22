import LRX.FiniteInversionDecomposition

namespace LRX.FiniteCuts
open scoped BigOperators
variable {k : ℕ}

theorem count_values_below {n : ℕ} (p : State n) (a : ℕ) :
    (∑ i : Fin n, if (p i).val < a then (1 : ℕ) else 0)=min n a := by
  calc
    _ = ∑ i : Fin n, if i.val < a then (1 : ℕ) else 0 := Equiv.sum_comp p _
    _ = _ := by simp [Fin.card_filter_val_lt]

theorem rotate_castSucc (i : Fin k) : finRotate (k+1) i.castSucc=i.succ :=
  finRotate_of_lt i.isLt

/-- Moving the first position to the last changes only its inversion pairs. -/
theorem domain_rotation_inversions (p : State (k+1)) :
    inversionNumber (p*finRotate (k+1))+2*(p 0).val=inversionNumber p+k := by
  classical
  have hfirst := inversion_on_first p
  have hlast := inversion_on_last (fun i : Fin (k+1) => p (finRotate (k+1) i))
  simp only [rotate_castSucc,finRotate_last] at hlast
  have hlow : (∑ i : Fin k, if (p i.succ).val < (p 0).val then (1 : ℕ) else 0)=(p 0).val := by
    have h := count_values_below p (p 0).val
    rw [Fin.sum_univ_succ] at h
    simpa only [lt_self_iff_false,ite_false,zero_add,min_eq_right (le_of_lt (p 0).isLt)] using h
  have hsplit :
      (∑ i : Fin k, if (p i.succ).val < (p 0).val then (1 : ℕ) else 0)+
      (∑ i : Fin k, if (p 0).val < (p i.succ).val then (1 : ℕ) else 0)=k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin k, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hne : (p i.succ).val ≠ (p 0).val := by
          intro h
          have hi := p.injective (Fin.ext h)
          have hv := congrArg Fin.val hi
          simp only [Fin.val_succ,Fin.val_zero] at hv
          omega
        split_ifs <;> omega
      _ = k := by simp
  change inversionNumber p=_ at hfirst
  change inversionNumber (p*finRotate (k+1))=_ at hlast
  omega

theorem value_rotation_inversions (p : State (k+1)) :
    inversionNumber ((finRotate (k+1))⁻¹*p)+2*(p⁻¹ 0).val=inversionNumber p+k := by
  have h := domain_rotation_inversions p⁻¹
  have he : p⁻¹*finRotate (k+1)=((finRotate (k+1))⁻¹*p)⁻¹ := by simp
  rw [he,inversion_number_inverse,inversion_number_inverse] at h
  exact h

#print axioms domain_rotation_inversions
#print axioms value_rotation_inversions
end LRX.FiniteCuts
