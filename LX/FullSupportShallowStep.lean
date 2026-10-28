import LX.ShallowNeighborSplice
import Mathlib

namespace LX.Core.FiniteCuts
variable {n : ℕ}

theorem full_carrier_neighbor_unit {x y : Fin n}
    (h : ZeroGap.RankAdjacent Finset.univ x y) : |(y : ℤ)-(x : ℤ)|=1 := by
  by_contra hunit
  have hne : x.val ≠ y.val := fun he => h.2.2.1 (Fin.ext he)
  have hgap : min x.val y.val+1 < max x.val y.val := by
    simp only [abs_eq_max_neg] at hunit
    omega
  let z : Fin n := ⟨min x.val y.val+1,by have := x.isLt; have := y.isLt; omega⟩
  apply h.2.2.2 z (Finset.mem_univ z)
  change min x.val y.val < min x.val y.val+1 ∧ min x.val y.val+1 < max x.val y.val
  exact ⟨by omega,hgap⟩


end LX.Core.FiniteCuts
