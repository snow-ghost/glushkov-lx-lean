import LRX.FiniteWindowInversions
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Cycle defect in physical finite coordinates. -/
def cycleDefect (p : State n) : ℤ :=
  (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)


end LRX.FiniteCuts

namespace LRX.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ}


end LRX.FiniteWindow
