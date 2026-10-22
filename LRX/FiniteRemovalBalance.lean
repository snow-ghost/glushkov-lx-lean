import LRX.PrunedExactService
import LRX.PrunedPartition

/-! Removing finite canonical cycles from a balanced periodic lift leaves a
balanced root lift; balance need not be assumed again for the retained part. -/
namespace LRX.PrunedLift
open scoped BigOperators
variable {n : ℕ}

theorem balance_of_finite_removal {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ)) :
    (∑ i ∈ S, d i)=0 := by
  have hcompl : (∑ i ∈ Sᶜ, d i)=0 := by
    calc
      (∑ i ∈ Sᶜ, d i)=∑ i ∈ Sᶜ, ((p.symm i : ℤ)-(i : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hfinite i (Finset.mem_compl.mp hi)
      _ = 0 := canonical_balance p Sᶜ (complement_invariant p S hS)
  have hsum := Finset.sum_add_sum_compl S d
  rw [hcompl,add_zero,hd.1] at hsum
  exact hsum

#print axioms balance_of_finite_removal
end LRX.PrunedLift
