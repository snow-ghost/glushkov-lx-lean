import LX.MinimumHeadObstruction
import LX.MinimumSmallGap
import LX.ThresholdDropBudget
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- If an unpaid minimum head lies in the terminal window, the preceding
raw offset is unoccupied and has normalized height exactly h+1. All
occupied phases of that height lie strictly below this cut. -/
theorem odd_unpaid_head_predecessor_cut (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p a ≤ (p 0-1).val ∧ p 0 ≠ p 0-1 ∧
      thresholdHeight p (p 0-1)=height p a+1 ∧
      (∀ b,p b-b ≠ p 0-1) ∧
      (∀ b,height p b=height p a+1 → (p b-b).val < (p 0-1).val) := by
  classical
  let F := (fixedPositions (permutation p 0)).card
  let g := (-p 0).val
  have hf : g+2 ≤ F := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p 0 (by omega) (by omega)
      (by change F ≤ _; simp only [zero_sub]; omega)
    have hr := anchor_reserve_nonneg p 0
    simp only [zero_sub] at hprice
    exact hunpaid ⟨w,hw,by omega⟩
  have hF : F ≤ 4 := (rank_peak_anchor_bounds p a 3 hmin hR).2 0
  have hgsmall : g ≤ 2 := by omega
  have hp0 : p 0 ≠ 0 := by intro he; simp only [he,neg_zero,Fin.val_zero] at hg1; omega
  have hgv : g=n-(p 0).val := by dsimp only [g]; simp [Fin.val_neg,hp0]
  have hpv := (p 0).isLt
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hneg1 : (-(1 : Fin n)).val=n-1 := by
    rw [Fin.val_neg,ite_eq_right (by intro he; have hv := congrArg Fin.val he; rw [hv1,Fin.val_zero] at hv; omega),hv1]
  have hcutval : (p 0-1).val=(p 0).val-1 := by
    rw [Fin.coe_sub_iff_le.mpr (show (1 : Fin n) ≤ p 0 by change (1 : Fin n).val ≤ (p 0).val; omega),hv1]
  have hbelow (k : ℕ) (hk : 0 < k) : F ≤ belowCount p 0 k := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p 0 i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; exact hk⟩
  have hmin0 : ∀ b,height p 0 ≤ height p b := by intro b; rw [hhead]; exact hmin b
  have hprelo := rank_surplus_nonnegative p 0 hmin0 (n-1) (by omega)
  have hcnt : belowCount p 0 (n-1) ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hprehi : rankSurplus p 0 (n-1) ≤ 1 := by unfold rankSurplus; omega
  have hprenz : rankSurplus p 0 (n-1) ≠ 0 := by
    intro hz
    obtain ⟨b,hb,hbh⟩ := zero_surplus_anchor p 0 hmin0 (-1) (by rwa [hneg1])
    have hraw : p b-b=p 0-1 := by
      unfold cyclicOffset at hb
      simp only [sub_zero] at hb
      linear_combination hb
    have hgap : (b-p b).val=g+1 := by
      have he : b-p b=(-p 0)+1 := by linear_combination -hraw
      rw [he,Fin.val_add,hv1,Nat.mod_eq_of_lt (by change g+1<n; omega)]
    have hnothead : p 0 ≠ p b-b := by
      intro he
      rw [hraw] at he
      have hone : (1 : Fin n)=0 := by linear_combination he
      have hv := congrArg Fin.val hone
      rw [hv1,Fin.val_zero] at hv
      omega
    have hbad := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin (hbh.trans hhead) hnothead hunpaid
    omega
  have hpre : rankSurplus p 0 (n-1)=1 := by omega
  have hcount : belowCount p 0 (n-1)=n := by unfold rankSurplus at hpre; omega
  have hunoccupied (b : Fin n) : p b-b ≠ p 0-1 := by
    intro hraw
    have hb : cyclicOffset p 0 b= -1 := by
      unfold cyclicOffset
      simp only [sub_zero]
      linear_combination hraw
    let S := Finset.univ.filter fun i : Fin n => (cyclicOffset p 0 i).val < n-1
    have hSc : S.card=n := hcount
    have hSe : S=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [Finset.card_univ,Fintype.card_fin,hSc])
    have hbin : b ∈ S := hSe.symm ▸ Finset.mem_univ b
    have hbv := (Finset.mem_filter.mp hbin).2
    rw [hb,hneg1] at hbv
    omega
  have hcut : thresholdHeight p (p 0-1)=height p a+1 := by
    have ht := threshold_height_rank p 0 (p 0-1)
    have he : (p 0-1)-(p 0-0)= -(1 : Fin n) := by ring
    rw [he,hneg1,hpre,hhead] at ht
    omega
  refine ⟨by omega,?_,hcut,hunoccupied,?_⟩
  · intro he
    have hv := congrArg Fin.val he
    rw [hcutval] at hv
    omega
  · intro b hbh
    by_contra hnot
    have hne := hunoccupied b
    have hvne : (p b-b).val ≠ (p 0-1).val := fun he => hne (Fin.ext he)
    have hrawlo : (p 0).val ≤ (p b-b).val := by omega
    by_cases heq : p b-b=p 0
    · have heh := equal_raw_offset_height p b 0 (by simpa using heq)
      omega
    have hrawne : (p b-b).val ≠ (p 0).val := fun he => heq (Fin.ext he)
    have hoff : (cyclicOffset p 0 b).val=(p b-b).val-(p 0).val := by
      unfold cyclicOffset
      simp only [sub_zero]
      rw [Fin.coe_sub_iff_le.mpr (show p 0 ≤ p b-b from hrawlo)]
    have hrn := (p b-b).isLt
    have hpos : 0 < (cyclicOffset p 0 b).val := by omega
    have hb := hbelow (cyclicOffset p 0 b).val hpos
    have ht := reanchor_height p 0 b
    rw [hhead,hbh] at ht
    omega

#print axioms odd_unpaid_head_predecessor_cut
end LX.AnchoredPhases
