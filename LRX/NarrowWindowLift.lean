import LRX.AffineLift
import Mathlib

/-! In a window no wider than half the circle, a strictly short lift has the
canonical finite displacements. The no-winding premise is derived here. -/
namespace LRX.FiniteWindow
variable {n b : ℕ} [NeZero n]


omit [NeZero n] in
theorem majorized_short {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (i : Fin n) :
    2*|d i| < (n : ℤ) := by
  have h := AffineLift.short_coordinates hd.1 hm i
  by_cases hi : 0 ≤ d i
  · rw [abs_of_nonneg hi]; omega
  · rw [abs_of_neg (by omega : d i < 0)]; omega

open scoped BigOperators

end LRX.FiniteWindow
