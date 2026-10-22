import LX.ZeroExchangeReserve
import LRX.EventDefectParity
import LRX.TwoWindowCycleDefect

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
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
    LRX.FiniteCuts.shiftedLiftPermutation p.symm (phase p a) (height p a)=permutation p a := by
  apply Equiv.ext
  intro i
  change p i+((phase p a+(height p a : ℤ) : ℤ) : Fin n)=p i+(a-p a)
  simp only [phase,Int.cast_add,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self]
  ring

/-- The reserve splits into two nonnegative quantities already defined on
finite permutations in LRX: event defect and excess reflection rank. -/
theorem anchor_reserve_decomposition (p : State n) (a : Fin n) :
    anchorReserve p a=LRX.FiniteCuts.cycleDefect (permutation p a)+
      ((permutation p a).support.card : ℤ)-(permutation p a).cycleFactorsFinset.card-height p a := by
  have hf := LRX.FiniteCuts.shifted_lift_inversion_formula (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hf
  change (inversions (displacement p a) : ℤ)=_ at hf
  have hm := LRX.FiniteCuts.displacement_mass_eq_twice_leftDepth (permutation p a)
  unfold anchorReserve LRX.FiniteCuts.cycleDefect
  nlinarith

theorem anchor_cycle_defect_bounds (p : State n) (a : Fin n) :
    0 ≤ LRX.FiniteCuts.cycleDefect (permutation p a) ∧
      LRX.FiniteCuts.cycleDefect (permutation p a) ≤ anchorReserve p a := by
  have hr := LRX.FiniteCuts.finite_depth_rank (permutation p a)
  have hc := LRX.FiniteCuts.descending_count_add_cycles_le_support (permutation p a)
  have hd := anchor_reserve_decomposition p a
  change height p a+(permutation p a).cycleFactorsFinset.card ≤ (permutation p a).support.card at hc
  constructor
  · unfold LRX.FiniteCuts.cycleDefect
    omega
  · omega

/-- Zero or one unit of reserve forces the finite event defect to vanish.
No shallow-cycle hypothesis is supplied by the caller. -/
theorem small_anchor_reserve_zero_defect (p : State n) (a : Fin n)
    (hsmall : anchorReserve p a ≤ 1) :
    LRX.FiniteCuts.cycleDefect (permutation p a)=0 := by
  have hb := anchor_cycle_defect_bounds p a
  obtain ⟨k,hk⟩ := LRX.FiniteCuts.finite_cycle_defect_even (permutation p a)
  change LRX.FiniteCuts.cycleDefect (permutation p a)=k+k at hk
  omega

/-- Majorization supplies the lower support bound. Thus unit reserve leaves
at most two vertices beyond the size accounted for by transposition cycles. -/
theorem unit_anchor_reserve_rigidity (p : State n) (a : Fin n)
    (hmaj : Majorized (displacement p a)) (hunit : anchorReserve p a=1) :
    LRX.FiniteCuts.cycleDefect (permutation p a)=0 ∧
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
  have hs := LRX.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  have hc := LRX.FiniteCuts.twice_cycle_count_le_support (permutation p a)
  exact ⟨hz,by omega,by omega,by omega,by omega⟩

/-- The strip reserve and the dimension-wide reserve are compared explicitly;
they must not be identified in the lower-height parity branch. -/
theorem anchor_reserve_le_dimension_reserve (p : State n) (a : Fin n)
    (hmaj : Majorized (displacement p a)) :
    anchorReserve p a ≤ ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) := by
  have hh := (short_coordinates (is_lift p a).1 hmaj a).2
  rw [displacement_anchor] at hh
  have hparity : (n : ℤ)=2*((n/2 : ℕ) : ℤ) ∨ (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by omega
  unfold anchorReserve
  rcases hparity with he | ho
  · have hp := mul_nonneg
      (show (0 : ℤ) ≤ ((n/2 : ℕ) : ℤ)-height p a by omega)
      (show (0 : ℤ) ≤ ((n/2 : ℕ) : ℤ)-height p a-1 by omega)
    nlinarith
  · nlinarith [sq_nonneg (((n/2 : ℕ) : ℤ)-height p a)]

theorem majorized_cycle_excess_bound (p : State n) (a : Fin n)
    (hmaj : Majorized (displacement p a)) :
    ((permutation p a).support.card : ℤ)-2*(permutation p a).cycleFactorsFinset.card ≤
      2*anchorReserve p a := by
  have hd := anchor_reserve_decomposition p a
  have hnonneg := (anchor_cycle_defect_bounds p a).1
  have hh := (short_coordinates (is_lift p a).1 hmaj a).2
  rw [displacement_anchor] at hh
  have hext := majorized_negative_level_count (is_lift p a).1 hmaj (height p a : ℤ) (by omega)
  have hs := LRX.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  omega

/-- This conclusion uses the actual dimension-wide reserve of the global
minimum, so it applies directly to the next unpaid branch. -/
theorem small_global_reserve_rigidity {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    LRX.FiniteCuts.cycleDefect (permutation p a)=0 ∧
      ((permutation p a).support.card : ℤ)-2*(permutation p a).cycleFactorsFinset.card ≤ 2 := by
  have hm := global_minimum_majorized ha
  have ha' := (anchor_reserve_le_dimension_reserve p a hm).trans hsmall
  exact ⟨small_anchor_reserve_zero_defect p a ha',
    (majorized_cycle_excess_bound p a hm).trans (by omega)⟩

/-- A cycle of length at least three uses at most three times its excess
over a transposition. Summing uses the actual disjoint cycle factorization. -/
theorem nonpair_cycle_mass_bound (q : State n) :
    ((∑ g ∈ q.cycleFactorsFinset.filter (fun g => g.support.card ≠ 2),g.support.card : ℕ) : ℤ) ≤
      3*((q.support.card : ℤ)-2*q.cycleFactorsFinset.card) := by
  classical
  have hterm (g : State n) (hg : g ∈ q.cycleFactorsFinset) :
      (if g.support.card ≠ 2 then (g.support.card : ℤ) else 0) ≤ 3*((g.support.card : ℤ)-2) := by
    have hc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1.two_le_card_support
    split_ifs <;> omega
  have hs := Finset.sum_le_sum hterm
  have htotal : (∑ g ∈ q.cycleFactorsFinset,(g.support.card : ℤ))=(q.support.card : ℤ) := by
    exact_mod_cast LRX.FiniteCuts.cycle_support_card_sum q
  have hr : (∑ g ∈ q.cycleFactorsFinset,3*((g.support.card : ℤ)-2))=
      3*((q.support.card : ℤ)-2*q.cycleFactorsFinset.card) := by
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,htotal]
    simp [mul_comm]
  rw [hr] at hs
  simpa only [Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] using hs

/-- In the unit-reserve branch all nontransposition cycles together occupy
at most six positions. The other cycles still require geometric routing. -/
theorem small_global_reserve_nonpair_mass {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    (∑ g ∈ (permutation p a).cycleFactorsFinset.filter (fun g => g.support.card ≠ 2),g.support.card) ≤ 6 := by
  have hh := (small_global_reserve_rigidity ha hsmall).2
  have hm := nonpair_cycle_mass_bound (permutation p a)
  omega

#print axioms anchor_reserve_decomposition
#print axioms anchor_cycle_defect_bounds
#print axioms small_anchor_reserve_zero_defect
#print axioms unit_anchor_reserve_rigidity
#print axioms small_global_reserve_rigidity
#print axioms small_global_reserve_nonpair_mass
end LX.AnchoredPhases
