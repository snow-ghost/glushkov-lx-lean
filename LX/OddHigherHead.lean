import LX.OddNonminimumHead

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The head is genuinely an exception in the terminal window: it has
height exactly one above the minimum and a positive small gap. -/
theorem rank_two_unpaid_higher_head (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p 0=height p a+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ 3 := by
  have hK := rank_two_unpaid_no_head_predecessor p a hn hh hmin hR hunpaid
  have hbound := odd_unpaid_second_excess_head_bound p a hn hh hmin hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hT : RelevantTerminalHead p (height p a) := by
    by_contra hnot
    rw [ite_eq_right hK,ite_eq_right hnot] at hbound
    split_ifs at hbound <;> omega
  have hhhead := rank_two_unpaid_head_not_minimum p a hn hh hmin hR hunpaid
  have hhead : height p 0=height p a+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ height p a+3 := by
    rcases hT with hT | hT
    · omega
    · exact hT
  refine ⟨hhead.1,hhead.2.1,?_⟩
  obtain ⟨j,hjlo,hjhi,hj⟩ := rank_two_unpaid_head_range p a hn hh hmin hR hunpaid
  have hjneg : j < 0 := by
    by_contra hnot
    have hjcases : j=0 ∨ j=1 := by omega
    rcases hjcases with h0 | h1
    · have hp0 : p 0=0 := by simpa only [h0,Int.cast_zero] using hj
      simp only [hp0,neg_zero,Fin.val_zero] at hhead
      omega
    · have hp1 : p 0=1 := by simpa only [h1,Int.cast_one] using hj
      have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
      have hone : (1 : Fin n) ≠ 0 := by
        intro he; have hv := congrArg Fin.val he; rw [hv1,Fin.val_zero] at hv; omega
      have hneg : (-p 0).val=n-1 := by rw [hp1,Fin.val_neg,ite_eq_right hone,hv1]
      omega
  have hval : ((-j).toNat : ℤ)= -j := Int.toNat_of_nonneg (by omega)
  have hkn : (-j).toNat < n := by omega
  have he : -p 0=((-j).toNat : Fin n) := by
    calc
      -p 0=((-j : ℤ) : Fin n) := by rw [hj,Int.cast_neg]
      _=((((-j).toNat : ℤ)) : Fin n) := congrArg (fun z : ℤ => (z : Fin n)) hval.symm
      _=((-j).toNat : Fin n) := by rw [Int.cast_natCast]
  rw [he,show ((-j).toNat : Fin n).val=(-j).toNat from Nat.mod_eq_of_lt hkn]
  omega

/-- The higher head occurs strictly before the aligned finish. -/
theorem rank_two_unpaid_head_before_aligned_finish (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    (-p 0).val < (b-p b).val ∧
      (cyclicOffset p b 0).val=(b-p b).val-(-p 0).val := by
  obtain ⟨_,hdpos,hdcap⟩ := rank_two_unpaid_higher_head p a hn hh hmin hR hunpaid
  obtain ⟨_,hFcap,_,_,hkpos,hkcap⟩ := rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  have he : cyclicOffset p b 0=(b-p b)-(-p 0) := by unfold cyclicOffset; ring
  have hv := Fin.intCast_val_sub_eq_sub_add_ite (b-p b) (-p 0)
  rw [← he] at hv
  have hle : -p 0 ≤ b-p b := by
    by_contra hnot
    rw [ite_eq_right hnot] at hv
    omega
  rw [ite_eq_left hle] at hv
  exact ⟨by omega,by omega⟩

#print axioms rank_two_unpaid_higher_head
#print axioms rank_two_unpaid_head_before_aligned_finish
end LX.AnchoredPhases
