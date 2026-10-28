import LX.FiniteWindowInversions
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Cycle defect in physical finite coordinates. -/
def cycleDefect (p : State n) : ℤ :=
  (∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
    (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)


end LX.Core.FiniteCuts

namespace LX.Core.FiniteWindow
open FiniteCuts
open scoped BigOperators
variable {n : ℕ}


end LX.Core.FiniteWindow
