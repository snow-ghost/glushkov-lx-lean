import LX.EventDefectParity
import LX.MajorizedExtremeCount
import LX.StrictBandEquality
import LX.TwoWindowCycleDefect
import LX.AnchoredPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Reserve relative to the capacity of this actual anchor's strip. It need
not equal the reserve relative to the dimension-wide maximum. -/
def anchorReserve (p : State n) (a : Fin n) : ℤ :=
  (height p a : ℤ)*((n : ℤ)-height p a-1)-inversions (displacement p a)

theorem anchor_reserve_nonneg (p : State n) (a : Fin n) : 0 ≤ anchorReserve p a := by
  have hh := (candidate_price_components p a).1
  unfold anchorReserve
  omega

theorem shifted_anchor_permutation (p : State n) (a : Fin n) :
    LX.Core.FiniteCuts.shiftedLiftPermutation p.symm (phase p a) (height p a)=permutation p a := by
  apply Equiv.ext
  intro i
  change p i+((phase p a+(height p a : ℤ) : ℤ) : Fin n)=p i+(a-p a)
  simp only [phase,Int.cast_add,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
  ring

/-- The reserve splits into two nonnegative quantities already defined on
finite permutations in LX.Core: event defect and excess reflection rank. -/
theorem anchor_reserve_decomposition (p : State n) (a : Fin n) :
    anchorReserve p a=LX.Core.FiniteCuts.cycleDefect (permutation p a)+
      ((permutation p a).support.card : ℤ)-(permutation p a).cycleFactorsFinset.card-height p a := by
  have hf := LX.Core.FiniteCuts.shifted_lift_inversion_formula (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hf
  change (inversions (displacement p a) : ℤ)=_ at hf
  have hm := LX.Core.FiniteCuts.displacement_mass_eq_twice_leftDepth (permutation p a)
  unfold anchorReserve LX.Core.FiniteCuts.cycleDefect
  nlinarith

theorem anchor_cycle_defect_bounds (p : State n) (a : Fin n) :
    0 ≤ LX.Core.FiniteCuts.cycleDefect (permutation p a) ∧
      LX.Core.FiniteCuts.cycleDefect (permutation p a) ≤ anchorReserve p a := by
  have hr := LX.Core.FiniteCuts.finite_depth_rank (permutation p a)
  have hc := LX.Core.FiniteCuts.descending_count_add_cycles_le_support (permutation p a)
  have hd := anchor_reserve_decomposition p a
  change height p a+(permutation p a).cycleFactorsFinset.card ≤ (permutation p a).support.card at hc
  constructor
  · unfold LX.Core.FiniteCuts.cycleDefect
    omega
  · omega

/-- Zero or one unit of reserve forces the finite event defect to vanish.
No shallow-cycle hypothesis is supplied by the caller. -/
theorem small_anchor_reserve_zero_defect (p : State n) (a : Fin n)
    (hsmall : anchorReserve p a ≤ 1) :
    LX.Core.FiniteCuts.cycleDefect (permutation p a)=0 := by
  have hb := anchor_cycle_defect_bounds p a
  obtain ⟨k,hk⟩ := LX.Core.FiniteCuts.finite_cycle_defect_even (permutation p a)
  change LX.Core.FiniteCuts.cycleDefect (permutation p a)=k+k at hk
  omega

/-- Majorization supplies the lower support bound. Thus unit reserve leaves
at most two vertices beyond the size accounted for by transposition cycles. -/
theorem unit_anchor_reserve_rigidity (p : State n) (a : Fin n)
    (hmaj : Majorized (displacement p a)) (hunit : anchorReserve p a=1) :
    LX.Core.FiniteCuts.cycleDefect (permutation p a)=0 ∧
      ((permutation p a).support.card : ℤ)-(permutation p a).cycleFactorsFinset.card=
        (height p a : ℤ)+1 ∧
      2*(height p a : ℤ) ≤ (permutation p a).support.card ∧
      ((permutation p a).support.card : ℤ) ≤ 2*height p a+2 ∧
      ((permutation p a).support.card : ℤ)-2*(permutation p a).cycleFactorsFinset.card ≤ 2 := by
  have hz := small_anchor_reserve_zero_defect p a (by omega)
  have hd := anchor_reserve_decomposition p a
  rw [hz,hunit,zero_add] at hd
  have hh := (short_coordinates (is_lift p a).1 hmaj a).2
  rw [displacement_anchor] at hh
  have hext := majorized_negative_level_count (is_lift p a).1 hmaj (height p a : ℤ) (by omega)
  have hs := LX.Core.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  have hc := LX.Core.FiniteCuts.twice_cycle_count_le_support (permutation p a)
  exact ⟨hz,by omega,by omega,by omega,by omega⟩


#print axioms anchor_reserve_decomposition
#print axioms anchor_cycle_defect_bounds
#print axioms small_anchor_reserve_zero_defect
#print axioms unit_anchor_reserve_rigidity
end LX.AnchoredPhases
