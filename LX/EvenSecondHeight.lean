import LX.HeadReserve
import LX.MinimumHeightRanks
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem head_displacement_offset (p : State n) (a : Fin n) :
    displacement p a 0=(cyclicOffset p a 0 : ℤ)-height p a := by
  have he : permutation p a 0=cyclicOffset p a 0 := by
    change p 0+(a-p a)=p 0-0-(p a-a)
    abel
  simp only [displacement,LX.Core.FiniteCuts.clockwiseRepresentative,Fin.val_zero,Nat.not_lt_zero,
    ite_false,add_zero,Nat.cast_zero,sub_zero,he]

/-- Choosing an anchor with a different cyclic displacement from position 0
makes the initial head strictly shallower than the maximal depth. -/
theorem head_reserve_of_distinct_offset (p : State n) (a : Fin n)
    (ha : cyclicOffset p a 0 ≠ 0) : backwardDepth (displacement p a) 0 < height p a := by
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  by_contra hnot
  have he : backwardDepth (displacement p a) 0=height p a := by have := hmax 0; omega
  have hd := maximum_depth_displacement (is_lift p a) 0 (by intro i; rw [he]; exact hmax i)
  rw [he,head_displacement_offset] at hd
  have hv : (cyclicOffset p a 0).val=0 := by omega
  exact ha (Fin.ext hv)


end LX.AnchoredPhases
