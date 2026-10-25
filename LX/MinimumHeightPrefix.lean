import LX.AnchorReserveRigidity
import LX.FiniteDropBudget
import LX.OddUnitFixedNeighbors
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.FiniteDropBudget
variable {n : ℕ} [NeZero n]

/-- Minimum height permits at most one linear backward unit arrow. -/
theorem minimum_height_backward_units (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (backwardUnits (permutation p a)).card ≤ 1 := by
  classical
  have hr := minimum_height_ranks p a hmin (n-1) (by omega)
  let S := Finset.univ.filter fun i => (cyclicOffset p a i).val < n-1
  have hd : Disjoint S (backwardUnits (permutation p a)) := by
    apply Finset.disjoint_left.mpr
    intro i hs hu
    have hu : (permutation p a i).val+1=i.val := (Finset.mem_filter.mp hu).2
    have hv : (cyclicOffset p a i).val=n-1 := by
      rw [cyclic_offset_normalized,Fin.coe_sub_iff_lt.mpr
        (show permutation p a i < i by change (permutation p a i).val < i.val; omega)]
      omega
    have hs : (cyclicOffset p a i).val < n-1 := (Finset.mem_filter.mp hs).2
    omega
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ backwardUnits (permutation p a)))
  rw [Finset.card_union_of_disjoint hd,Finset.card_univ,Fintype.card_fin] at hc
  change n-1 ≤ S.card at hr
  have := NeZero.pos n
  omega

/-- The initial fixed interval is paid by the actual strip reserve. -/
theorem minimum_height_fixed_prefix_bound (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (r : ℕ) (hr : r < n)
    (hfix : ∀ i : Fin n,i.val < r → permutation p a i=i) :
    (r : ℤ) ≤ (n : ℤ)-2*height p a+anchorReserve p a := by
  have h := fixed_prefix_drop_bound (permutation p a) r hr hfix
  have hu := minimum_height_backward_units p a hmin
  have he := anchor_reserve_decomposition p a
  unfold LRX.FiniteCuts.cycleDefect at he
  change 3*(height p a : ℤ) ≤ _ at h
  rw [Nat.cast_sub (by omega : r ≤ n)] at h
  omega


#print axioms minimum_height_backward_units
#print axioms minimum_height_fixed_prefix_bound
end LX.AnchoredPhases
