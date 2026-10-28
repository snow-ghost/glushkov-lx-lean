import LX.EvenUnitPhaseParity
import LX.HeadReserve
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Maximum-depth tokens are exactly the fixed positions of the anchored
source. This identity does not require majorization. -/
theorem depth_eq_height_iff_fixed (p : State n) (a i : Fin n) :
    backwardDepth (displacement p a) i=height p a ↔ permutation p a i=i := by
  have hmax (j : Fin n) : backwardDepth (displacement p a) j ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 j
  constructor
  · intro hi
    have hh := maximum_depth_displacement (is_lift p a) i (by intro j; rw [hi]; exact hmax j)
    rw [hi,displacement_offset] at hh
    have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [cyclic_offset_normalized] at hz
    exact sub_eq_zero.mp hz
  · intro hi
    have hd := fixed_source_displacement p a i ((mem_fixedPositions _ _).mpr hi)
    have hr := displacement_add_depth (is_lift p a) i
    have hnonneg : 0 ≤ ∑ j,((LX.Core.AffineLift.crossing (displacement p a) i j).toNat : ℤ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    rw [hd] at hr
    have hh := hmax i
    omega

theorem top_depth_count_eq_fixed (p : State n) (a : Fin n) :
    depthCount (displacement p a) (height p a)=(fixedPositions (permutation p a)).card := by
  unfold depthCount fixedPositions
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  rw [← depth_eq_height_iff_fixed]
  omega


#print axioms top_depth_count_eq_fixed
end LX.AnchoredPhases
