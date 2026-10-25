import LX.OddNoHeadPredecessor
import Mathlib

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem rank_two_unpaid_smaller_aligned_exists (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    SmallerHigherAlignedTerminal p (height p a) := by
  have hK := rank_two_unpaid_no_head_predecessor p a hn hh hmin hR hunpaid
  have hbound := odd_unpaid_second_excess_smaller_phase_bound p a hn hh hmin hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  by_contra hnot
  rw [ite_eq_right hK,ite_eq_right hnot] at hbound
  omega

/-- No minimum-height head survives the complete odd window count. -/
theorem rank_two_unpaid_head_not_minimum (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : height p a < height p 0 := by
  have hle := hmin 0
  by_contra hnot
  have he : height p 0=height p a := by omega
  exact rank_two_unpaid_minimum_head_no_smaller p a hn hh hR he hunpaid
    (rank_two_unpaid_smaller_aligned_exists p a hn hh hmin hR hunpaid)


#print axioms rank_two_unpaid_smaller_aligned_exists
#print axioms rank_two_unpaid_head_not_minimum
end LX.AnchoredPhases
