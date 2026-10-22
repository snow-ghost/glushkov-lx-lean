import LX.OddCutWindow
import LX.ConjectureObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- At an actual peak, the triangular excess is contained in the same
second-excess sum used by the terminal cut count. -/
theorem rank_peak_second_excess (p : State n) (a r : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b) (hRpos : 0 < R)
    (hpeak : rankSurplus p a r.val=R) :
    ((R : ℤ)-1)*(R-2) ≤ 2*secondExcess p a := by
  have hb := minimum_count_minus_high_count p a r R hmin hRpos hpeak
  rw [← second_excess_count p a hmin] at hb
  exact hb

/-- The remaining odd counterexample geometry has peak at most four,
instead of six, and second excess strictly below the actual peak. -/
theorem odd_unpaid_four_rank_geometry (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 2 ≤ R ∧ R ≤ 4 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      secondExcess p a ≤ (R : ℤ)-1 ∧
      (R : ℤ)*(R-2) ≤ anchorReserve p a ∧ anchorReserve p a ≤ (height p a : ℤ) := by
  have hbase : 3*(n : ℤ)^2-8*n+9=4*(3*(m : ℤ)^2-m+1) := by
    have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
    rw [hn']; ring
  have hstrict : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(1 : ℤ)) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  obtain ⟨a,r,R,hnlarge,ha,hh,hmin,hRpos,_,hpeak,hR,hreserve,_,hodd⟩ :=
    conjecture_unpaid_reserve_geometry (by omega) p m 1 (by omega) hn hstrict
  have hres : (R : ℤ)*(R-2) ≤ anchorReserve p a := by
    convert hreserve using 1 <;> ring
  have hresup : anchorReserve p a ≤ (height p a : ℤ) := by
    have hb := (hodd rfl).2
    omega
  have hRsmall : R ≤ height p a+2 := by
    have hp := mul_nonneg (show 0 ≤ (R : ℤ)-1 by omega) (show 0 ≤ (R : ℤ)-2 by omega)
    nlinarith only [hp,hres,hresup]
  have hQ := odd_unpaid_cut_second_excess p a R (by omega) (by omega) hmin hR hRsmall hunpaid
  have htri := rank_peak_second_excess p a r R hmin (by omega) hpeak
  have hfour : R ≤ 4 := by
    by_contra hnot
    have hp := mul_nonneg (show 0 ≤ (R : ℤ)-5 by omega) (show 0 ≤ (R : ℤ) by positivity)
    nlinarith only [hp,htri,hQ]
  exact ⟨a,r,R,hnlarge,ha,hh,hmin,by omega,hfour,hpeak,hR,hQ,hres,hresup⟩

#print axioms rank_peak_second_excess
#print axioms odd_unpaid_four_rank_geometry
end LX.AnchoredPhases
