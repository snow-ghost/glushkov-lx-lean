import LRX.FiniteEntryContraction

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem matrix_sum_puncture (f : Fin (n+1) → Fin (n+1) → ℕ) (a : Fin (n+1))
    (hdiag : f a a=0) :
    (∑ i, ∑ j, f i j)=
      (∑ i : Fin n, ∑ j : Fin n, f (a.succAbove i) (a.succAbove j))+
      (∑ j, f a j)+(∑ i, f i a) := by
  have ht := Fin.sum_univ_succAbove (fun i => ∑ j, f i j) a
  have hi (i : Fin n) := Fin.sum_univ_succAbove (fun j => f (a.succAbove i) j) a
  have hc := Fin.sum_univ_succAbove (fun i => f i a) a
  simp_rw [hi] at ht
  rw [Finset.sum_add_distrib] at ht
  rw [hdiag,zero_add] at hc
  omega

def incidentInversions (p : State (n+1)) (a : Fin (n+1)) : ℕ :=
  (∑ j : Fin (n+1), if a.val < j.val ∧ (p j).val < (p a).val then 1 else 0)+
  (∑ i : Fin (n+1), if i.val < a.val ∧ (p a).val < (p i).val then 1 else 0)

theorem contract_preserves_pair_order (p : State (n+1)) (a : Fin (n+1)) (i j : Fin n) :
    (a.succAbove i).val < (a.succAbove j).val ∧ (p (a.succAbove j)).val < (p (a.succAbove i)).val ↔
      i.val < j.val ∧ (contract p a j).val < (contract p a i).val := by
  change (a.succAbove i < a.succAbove j ∧ p (a.succAbove j) < p (a.succAbove i)) ↔ _
  rw [← contract_entry p a i,← contract_entry p a j]
  simp only [Fin.succAbove_lt_succAbove_iff]
  rfl

/-- Only inversion pairs involving the removed source row disappear. -/
theorem contraction_inversion_price (p : State (n+1)) (a : Fin (n+1)) :
    inversionNumber p=inversionNumber (contract p a)+incidentInversions p a := by
  have h := matrix_sum_puncture
    (fun i j : Fin (n+1) => if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0) a (by simp)
  have hmiddle :
      (∑ i : Fin n, ∑ j : Fin n,
        if (a.succAbove i).val < (a.succAbove j).val ∧
          (p (a.succAbove j)).val < (p (a.succAbove i)).val then 1 else 0)=inversionNumber (contract p a) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [contract_preserves_pair_order]
  rw [hmiddle] at h
  simpa only [inversionNumber,incidentInversions,Nat.add_assoc] using h

#print axioms contraction_inversion_price
end LRX.FiniteCuts
