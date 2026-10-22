import LX.OddNoHeadPredecessor

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

/-- The remaining two phases have distinct gaps among the first four
positions, and the original head cannot have minimum height. -/
theorem odd_unpaid_distinct_small_phase_constraints (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ a b c : Fin n,n=2*height p a+3 ∧ 2 ≤ height p a ∧
      (∀ d,height p a ≤ height p d) ∧
      (∀ t : Fin n,rankSurplus p a t.val ≤ 2) ∧
      height p a < height p 0 ∧ HigherAlignedTerminal p (height p a) b ∧
      height p c=height p a+1 ∧
      0 < (c-p c).val ∧ (c-p c).val < (b-p b).val ∧ (b-p b).val ≤ 4 := by
  obtain ⟨a,_,hnlarge,_,hh,hmin,_,hR,_,_⟩ := odd_unpaid_rank_two_geometry hn5 p m hn hunpaid
  have hna : n=2*height p a+3 := by omega
  have hha : 2 ≤ height p a := by omega
  obtain ⟨b,c,hb,hc,hcg,hcb⟩ := rank_two_unpaid_smaller_aligned_exists p a hna hha hmin hR hunpaid
  have hg := rank_two_unpaid_aligned_gap p a b hna hha hR hb hunpaid
  exact ⟨a,b,c,hna,hha,hmin,hR,
    rank_two_unpaid_head_not_minimum p a hna hha hmin hR hunpaid,hb,hc,hcg,hcb,by omega⟩

#print axioms rank_two_unpaid_smaller_aligned_exists
#print axioms rank_two_unpaid_head_not_minimum
#print axioms odd_unpaid_distinct_small_phase_constraints
end LX.AnchoredPhases
