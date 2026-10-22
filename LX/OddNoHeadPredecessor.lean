import LX.OddAlignedMinimumHead

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The predecessor exception is impossible in the remaining rank-two
profile. Both possible head values force the aligned exception, which
in turn would force the incompatible value one. -/
theorem rank_two_unpaid_no_head_predecessor (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ¬ HeadPredecessorTerminal p (height p a) := by
  intro hK
  have hp := rank_two_unpaid_head_predecessor_values p a hn hh hmin hR hK hunpaid
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hsmall : (-p 0).val ≤ height p a+3 := by
    rcases hp with hp | hp
    · simp only [hp,neg_zero,Fin.val_zero]; omega
    · rw [hp,neg_neg,hv1]; omega
  have hbound := odd_unpaid_small_head_aligned_bound p a hn hh hmin
    (fun t => (hR t).trans (by omega)) hK.1 hsmall hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hJ : ∃ b,HigherAlignedTerminal p (height p a) b := by
    by_contra hnot
    rw [ite_eq_right hnot] at hbound
    omega
  obtain ⟨b,hb⟩ := hJ
  have hp1 := rank_two_unpaid_aligned_minimum_head p a b hn hh hR hK.1 hb hunpaid
  rcases hp with hp | hp
  · have hv := congrArg Fin.val (hp1.symm.trans hp)
    rw [hv1,Fin.val_zero] at hv
    omega
  · have hone : (1 : Fin n) ≠ 0 := by
      intro he; have hv := congrArg Fin.val he; rw [hv1,Fin.val_zero] at hv; omega
    have hv := congrArg Fin.val (hp1.symm.trans hp)
    rw [hv1,Fin.val_neg,ite_eq_right hone,hv1] at hv
    omega

theorem rank_two_unpaid_aligned_exists (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ b,HigherAlignedTerminal p (height p a) b := by
  have hK := rank_two_unpaid_no_head_predecessor p a hn hh hmin hR hunpaid
  have hbound := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  by_contra hnot
  rw [ite_eq_right hK,ite_eq_right hnot] at hbound
  omega

theorem rank_two_unpaid_minimum_head_value (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hhead : height p 0=height p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=1 := by
  obtain ⟨b,hb⟩ := rank_two_unpaid_aligned_exists p a hn hh hmin hR hunpaid
  exact rank_two_unpaid_aligned_minimum_head p a b hn hh hR hhead hb hunpaid

#print axioms rank_two_unpaid_no_head_predecessor
#print axioms rank_two_unpaid_aligned_exists
#print axioms rank_two_unpaid_minimum_head_value
end LX.AnchoredPhases
