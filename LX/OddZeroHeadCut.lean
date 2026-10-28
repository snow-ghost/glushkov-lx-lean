import LX.MinimumSmallGap
import LX.ThresholdDropBudget
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A fixed minimum head also has an unoccupied predecessor threshold. -/
theorem odd_unpaid_zero_head_predecessor_cut (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hhead : height p 0=height p a) (hp0 : p 0=0)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p a ≤ (p 0-1).val ∧ p 0 ≠ p 0-1 ∧
      thresholdHeight p (p 0-1)=height p a+1 ∧
      (∀ b,p b-b ≠ p 0-1) ∧
      (∀ b,height p b=height p a+1 → (p b-b).val < (p 0-1).val) := by
  classical
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hone : (1 : Fin n) ≠ 0 := by intro he; have := congrArg Fin.val he; rw [hv1,Fin.val_zero] at this; omega
  have hneg1 : (-(1 : Fin n)).val=n-1 := by rw [Fin.val_neg,ite_eq_right hone,hv1]
  have hmin0 : ∀ b,height p 0 ≤ height p b := by intro b; rw [hhead]; exact hmin b
  have hprelo := rank_surplus_nonnegative p 0 hmin0 (n-1) (by omega)
  have hcnt : belowCount p 0 (n-1) ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hprenz : rankSurplus p 0 (n-1) ≠ 0 := by
    intro hz
    obtain ⟨b,hb,hbh⟩ := zero_surplus_anchor p 0 hmin0 (-1) (by rwa [hneg1])
    have hraw : p b-b= -1 := by simpa only [cyclicOffset,hp0,sub_zero] using hb
    have hgap : (b-p b).val=1 := by
      have he : b-p b=(1 : Fin n) := by linear_combination -hraw
      rw [he,hv1]
    have hnothead : p 0 ≠ p b-b := by rw [hp0,hraw]; exact Ne.symm (neg_ne_zero.mpr hone)
    have hbad := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin (hbh.trans hhead) hnothead hunpaid
    omega
  have hpre : rankSurplus p 0 (n-1)=1 := by unfold rankSurplus at *; omega
  have hcount : belowCount p 0 (n-1)=n := by unfold rankSurplus at hpre; omega
  have hunoccupied (b : Fin n) : p b-b ≠ p 0-1 := by
    intro hraw
    have hb : cyclicOffset p 0 b= -1 := by simp only [cyclicOffset,hp0,sub_zero]; simpa only [hp0,zero_sub] using hraw
    let S := Finset.univ.filter fun i : Fin n => (cyclicOffset p 0 i).val < n-1
    have hSc : S.card=n := hcount
    have hSe : S=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [Finset.card_univ,Fintype.card_fin,hSc])
    have hbin : b ∈ S := hSe.symm ▸ Finset.mem_univ b
    have hbv := (Finset.mem_filter.mp hbin).2
    rw [hb,hneg1] at hbv
    omega
  have hcutval : (p 0-1).val=n-1 := by rw [hp0,zero_sub,hneg1]
  have hcut : thresholdHeight p (p 0-1)=height p a+1 := by
    have ht := threshold_height_rank p 0 (p 0-1)
    have he : (p 0-1)-(p 0-0)= -(1 : Fin n) := by ring
    rw [he,hneg1,hpre,hhead] at ht
    omega
  refine ⟨by omega,?_,hcut,hunoccupied,?_⟩
  · rw [hp0,zero_sub]
    exact Ne.symm (neg_ne_zero.mpr hone)
  · intro b _
    have hne : (p b-b).val ≠ (p 0-1).val := fun he => hunoccupied b (Fin.ext he)
    have := (p b-b).isLt
    omega

#print axioms odd_unpaid_zero_head_predecessor_cut
end LX.AnchoredPhases
