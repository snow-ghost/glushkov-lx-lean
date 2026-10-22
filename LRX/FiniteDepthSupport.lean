import LRX.FiniteDepthRank

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- The exact finite depth bound and the minimum cycle size give the support bound. -/
theorem finite_depth_support (p : State n) :
    2*(inversionNumber p : ℤ)+(p.support.card : ℤ) ≤ 2*(∑ i : Fin n, |displacement p i|) := by
  have hr := finite_depth_rank p
  have hc : 2*(p.cycleFactorsFinset.card : ℤ) ≤ (p.support.card : ℤ) := by
    exact_mod_cast twice_cycle_count_le_support p
  omega

#print axioms finite_depth_support
end LRX.FiniteCuts
