import Mathlib

/-! Exact subset capacity for injective integer coordinates in a finite
interval. The endpoints need not be consecutive. -/
namespace LRX.FiniteCoordinates
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem range_sum_twice (k : ℕ) : 2*(∑ i ∈ Finset.range k, (i : ℤ))=(k : ℤ)*(k-1) := by
  by_cases hk : k=0
  · simp [hk]
  · have h := Finset.sum_range_id_mul_two k
    have hz := congrArg (fun a : ℕ => (a : ℤ)) h
    push_cast at hz
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hz
    norm_num at hz
    nlinarith


end LRX.FiniteCoordinates
