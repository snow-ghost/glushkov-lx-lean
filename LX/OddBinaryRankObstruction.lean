import LX.OddPositiveExcessHead
import LX.OddThreeRankObstruction
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The rank-three branch is completely excluded. Every remaining odd
input has rank surplus only zero, one, or two, and no second excess. -/
theorem odd_unpaid_rank_two_geometry (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ a r : Fin n,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ rankSurplus p a r.val=2 ∧
      (∀ t : Fin n,rankSurplus p a t.val ≤ 2) ∧ secondExcess p a=0 ∧
      anchorReserve p a ≤ (height p a : ℤ) := by
  obtain ⟨a,r,R,hnlarge,ha,hh,hmin,hRlo,hRhi,hpeak,hR,hcases,_,hresup⟩ :=
    odd_unpaid_three_rank_geometry hn5 p m hn hunpaid
  have hs := odd_unpaid_second_excess_zero p a (by omega) (by omega) hmin
    (fun t => (hR t).trans (by exact_mod_cast hRhi)) hunpaid
  have he : R=2 := by rcases hcases with hc | hc <;> omega
  rw [he] at hpeak hR
  exact ⟨a,r,hnlarge,ha,hh,hmin,hpeak,hR,hs,hresup⟩


#print axioms odd_unpaid_rank_two_geometry
end LX.AnchoredPhases
