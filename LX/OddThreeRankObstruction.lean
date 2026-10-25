import LX.OddFourRankObstruction
import LX.OddWideCutCount
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The peak-four branch is impossible. The remaining odd inputs have
either a binary-high profile (peak two), or exactly one rank-three
thresholds. All conditions are extracted from the actual input. -/
theorem odd_unpaid_three_rank_geometry (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 2 ≤ R ∧ R ≤ 3 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      ((R=2 ∧ secondExcess p a=0) ∨ (R=3 ∧ secondExcess p a=1)) ∧
      (R : ℤ)*(R-2) ≤ anchorReserve p a ∧ anchorReserve p a ≤ (height p a : ℤ) := by
  obtain ⟨a,r,R,hnlarge,ha,hh,hmin,hRlo,hRhi,hpeak,hR,_,hres,hresup⟩ :=
    odd_unpaid_four_rank_geometry hn5 p m hn hunpaid
  have hQ := odd_unpaid_second_excess_le_one p a (by omega) (by omega) hmin hunpaid
  have htri := rank_peak_second_excess p a r R hmin (by omega) hpeak
  have hthree : R ≤ 3 := by
    by_contra hnot
    have hfour : R=4 := by omega
    rw [hfour] at htri
    norm_num at htri
    omega
  refine ⟨a,r,R,hnlarge,ha,hh,hmin,hRlo,hthree,hpeak,hR,?_,hres,hresup⟩
  have hc : R=2 ∨ R=3 := by omega
  rcases hc with hc | hc
  · refine Or.inl ⟨hc,?_⟩
    unfold secondExcess
    apply Finset.sum_eq_zero
    intro t _
    have ht := hR t
    rw [hc] at ht
    omega
  · refine Or.inr ⟨hc,?_⟩
    rw [hc] at htri
    norm_num at htri
    omega


#print axioms odd_unpaid_three_rank_geometry
end LX.AnchoredPhases
