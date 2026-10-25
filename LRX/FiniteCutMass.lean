import LRX.FiniteCuts
import Mathlib

/-! Double counting actual finite cut crossings gives the exact footrule. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem forward_as_sum (p : State b) (e : ℕ) :
    halfLoad p e=∑ i : Fin b, if i.val < e ∧ e ≤ (p i).val then 1 else 0 := by
  have hs : forward p e=Finset.univ.filter (fun i : Fin b => i.val < e ∧ e ≤ (p i).val) := by
    ext i; simp
  rw [halfLoad, hs]
  simpa using (Finset.sum_boole (R := ℕ)
    (fun i : Fin b => i.val < e ∧ e ≤ (p i).val) Finset.univ).symm

theorem backward_as_sum (p : State b) (e : ℕ) :
    (backward p e).card=∑ i : Fin b, if (p i).val < e ∧ e ≤ i.val then 1 else 0 := by
  have hs : backward p e=Finset.univ.filter (fun i : Fin b => (p i).val < e ∧ e ≤ i.val) := by
    ext i; simp
  rw [hs]
  simpa using (Finset.sum_boole (R := ℕ)
    (fun i : Fin b => (p i).val < e ∧ e ≤ i.val) Finset.univ).symm


#print axioms half_load_capacity
end LRX.FiniteCuts
