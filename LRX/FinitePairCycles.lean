import LRX.FiniteCycleSupportBudget
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Equality in the minimum cycle-size bound forces every cycle to be a swap. -/
theorem cycles_are_swaps_of_support_eq_twice_count (p : State n)
    (heq : p.support.card=2*p.cycleFactorsFinset.card) :
    ∀ q ∈ p.cycleFactorsFinset, q.IsSwap := by
  classical
  have hlo : ∀ q ∈ p.cycleFactorsFinset, 2 ≤ q.support.card :=
    fun q hq => (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1.two_le_card_support
  have hs : (∑ _q ∈ p.cycleFactorsFinset, 2)=∑ q ∈ p.cycleFactorsFinset, q.support.card := by
    rw [cycle_support_card_sum, heq]
    simp [Nat.mul_comm]
  have hall := (Finset.sum_eq_sum_iff_of_le hlo).mp hs
  intro q hq
  exact Equiv.Perm.card_support_eq_two.mp (hall q hq).symm

#print axioms cycles_are_swaps_of_support_eq_twice_count
end LRX.FiniteCuts
