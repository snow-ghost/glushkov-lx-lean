import LX.ConjectureRankReduction
import LX.EvenUnitConjecture
import LX.OddZeroReserveConjecture
import LX.ReflectionConjecture
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Necessary data of an actual counterexample to the parity conjecture.
The existence of these data alone is not sufficient for a counterexample. -/
theorem conjecture_unpaid_reserve_geometry (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 1+e ≤ R ∧ R+2*e ≤ 8 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      (R : ℤ)*(R-1-e) ≤ anchorReserve p a ∧
      (e=0 → 2 ≤ anchorReserve p a ∧ anchorReserve p a ≤ (n : ℤ)-3) ∧
      (e=1 → 1 ≤ anchorReserve p a ∧ anchorReserve p a ≤ (m : ℤ)-1) := by
  obtain ⟨a,r,R,hnlarge,ha,hh,hmin,hRpos,hRbound,hpeak,hR,_⟩ :=
    conjecture_unpaid_rank_geometry hn4 p m e he hn hunpaid
  have hRlower : 1+e ≤ R := by
    interval_cases e
    · omega
    · by_contra hnot
      have hs : (∑ t : Fin n,rankSurplus p a t.val) ≤ (n : ℤ)-1 := by
        calc
          _ ≤ ∑ t : Fin n,((1 : ℤ)-(if t=0 then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro t _
            by_cases ht : t=0
            · subst t
              simp [rankSurplus,belowCount]
            · rw [ite_eq_right ht]
              have := hR t
              omega
          _ = _ := by simp [Finset.sum_sub_distrib]
      have hmass := rank_surplus_sum p a
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hs,hmass,hn']
  have hrank := critical_rank_peak_reserve p a r ha e (by omega)
  rw [hpeak] at hrank
  refine ⟨a,r,R,hnlarge,ha,hh,hmin,hRlower,hRbound,hpeak,hR,hrank,?_,?_⟩
  · intro he0
    subst e
    have hpos : 1 ≤ anchorReserve p a := by
      by_contra hnot
      have hz : anchorReserve p a=0 := by have := anchor_reserve_nonneg p a; omega
      obtain ⟨w,hw,hprice⟩ := even_zero_reserve_conjecture_word p a ha hn4 (by omega) hz
      exact hunpaid ⟨w,hw,by norm_num; omega⟩
    have hpos2 : 2 ≤ anchorReserve p a := by
      by_contra hnot
      have hr1 : anchorReserve p a=1 := by omega
      obtain ⟨w,hw,hprice⟩ := even_one_reserve_conjecture_word p a hn4 ha (by omega) hr1
      exact hunpaid ⟨w,hw,by norm_num; omega⟩
    refine ⟨hpos2,?_⟩
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
      p (phase p a) (displacement p a) (is_lift p a) (global_minimum_majorized ha)
      (height p a) (by omega) (by omega)
      (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    apply hunpaid
    refine ⟨w,hw,?_⟩
    norm_num
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
    unfold anchorReserve at hnot
    nlinarith only [hprice,hnot,hn']
  · intro he1
    subst e
    have hpos : 1 ≤ anchorReserve p a := by
      by_contra hnot
      have hz : anchorReserve p a=0 := by have := anchor_reserve_nonneg p a; omega
      obtain ⟨w,hw,hprice⟩ := odd_zero_reserve_conjecture_word p a hn4 ha (by omega) hz
      exact hunpaid ⟨w,hw,by norm_num; omega⟩
    refine ⟨hpos,?_⟩
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
      p (phase p a) (displacement p a) (is_lift p a) (global_minimum_majorized ha)
      (height p a) (by omega) (by omega)
      (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    apply hunpaid
    refine ⟨w,hw,?_⟩
    norm_num
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
    have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
    unfold anchorReserve at hnot
    nlinarith only [hprice,hnot,hn',hm']

#print axioms conjecture_unpaid_reserve_geometry
end LX.AnchoredPhases
