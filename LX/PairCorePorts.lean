import LX.FixedCountReflection
import LX.AnchorReserveRigidity
import Mathlib

namespace LX.PairCore
variable {n : ℕ}

/-- Fixed points and the left endpoints of adjacent pairs hit every pair
interval of a noncrossing involution. -/
def ports (e : State n) : Finset (Fin n) :=
  LX.Core.FiniteCuts.fixedPositions e ∪ Finset.univ.filter (fun i => i.val+1=(e i).val)

theorem pair_hits_ports (e : State n) (hinv : Function.Involutive e)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs e) (a b : Fin n)
    (hab : a.val < b.val) (he : e a=b) :
    ∃ x ∈ ports e,a.val ≤ x.val ∧ x.val ≤ b.val := by
  by_cases hf : ∃ x : Fin n,a.val ≤ x.val ∧ x.val ≤ b.val ∧ e x=x
  · obtain ⟨x,hax,hxb,hx⟩ := hf
    refine ⟨x,Finset.mem_union_left _ ((LX.Core.FiniteCuts.mem_fixedPositions e x).mpr hx),hax,hxb⟩
  · have hfixed (x : Fin n) (hax : a.val ≤ x.val) (hxb : x.val ≤ b.val) : e x ≠ x := by
      intro hx
      exact hf ⟨x,hax,hxb,hx⟩
    obtain ⟨x,y,hax,hyb,hxy,hex⟩ := LX.Core.FiniteCuts.noncrossing_pair_contains_adjacent
      e hinv hnc a b hab he hfixed
    refine ⟨x,Finset.mem_union_right _ ?_,hax,by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hex]; exact hxy⟩


end LX.PairCore

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Small dimension-wide reserve forces height to be within one below the
largest half-size height; this is derived from the actual exchange count. -/
theorem small_dimension_reserve_height_gap (p : State n) (a : Fin n)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) : n ≤ 2*height p a+3 := by
  have hx := (candidate_price_components p a).1
  have hpar : (n : ℤ)=2*((n/2 : ℕ) : ℤ) ∨ (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by omega
  have hs : ((n : ℤ)-1-2*height p a)^2 ≤ 5 := by
    rcases hpar with he | ho <;> nlinarith
  by_contra hnot
  have hh : (3 : ℤ) ≤ (n : ℤ)-1-2*height p a := by omega
  nlinarith [sq_nonneg ((n : ℤ)-4-2*height p a)]

theorem majorized_anchor_fixed_positions (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) :
    ((LX.Core.FiniteCuts.fixedPositions (permutation p a)).card : ℤ) ≤ (n : ℤ)-2*height p a := by
  have hh := (short_coordinates (is_lift p a).1 hm a).2
  rw [displacement_anchor] at hh
  have hext := majorized_negative_level_count (is_lift p a).1 hm (height p a : ℤ) (by omega)
  have hs := LX.Core.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  have hf := LX.Core.FiniteCuts.fixed_positions_card (permutation p a)
  omega


end LX.AnchoredPhases
