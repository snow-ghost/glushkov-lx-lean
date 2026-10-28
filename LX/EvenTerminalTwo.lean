import LX.EvenBackwardSaturation
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem even_unpaid_small_gap_not_minimum (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12)
    (hg1 : 1 ≤ (b-p b).val) (hg2 : (b-p b).val ≤ 2) :
    height p b ≠ height p a := by
  intro hb
  have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
  have hf := (rank_peak_anchor_bounds p a 1 hmin hR).2 b
  obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega) (by omega)
  have hr := anchor_reserve_nonneg p b
  exact hunpaid ⟨w,hw,by omega⟩

/-- The terminal raw offset -2 is an occupied higher phase. Its singleton
representative moves forward or directly to zero. -/
theorem even_unpaid_terminal_two (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) :
    ∃ b : Fin n,height p b=height p a+1 ∧ p b-b= -2 ∧
      (fixedPositions (permutation p b)).card=1 ∧
      (b.val < (p b).val ∨ p b=0) ∧
      b.val+(-p b).val=2 ∧
      (∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val) := by
  classical
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hv2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (show 2<n by omega)]
  let t : Fin n := -2-(p a-a)
  have hR := even_unpaid_rank_at_most_one p a hn hh hmin hunpaid
  have ht0 : rankSurplus p a t.val ≠ 0 := by
    intro hz
    obtain ⟨b,hb,hheight⟩ := zero_surplus_anchor p a hmin t hz
    have hraw : p b-b= -2 := by dsimp only [t] at hb; unfold cyclicOffset at hb; linear_combination hb
    have hgap : (b-p b).val=2 := by
      have he : b-p b=(2 : Fin n) := by linear_combination -hraw
      rw [he,hv2]
    exact even_unpaid_small_gap_not_minimum p a b hn hh hmin hunpaid (by omega) (by omega) hheight
  have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
  have hone : rankSurplus p a t.val=1 := by have := hR t; omega
  have hex : ∃ b : Fin n,cyclicOffset p a b=t ∧ height p b=height p a+1 := by
    rcases rank_one_occupied_or_next_minimum p a t hmin hone with hb | ⟨b,hb,hheight⟩
    · exact hb
    have hraw : p b-b= -1 := by dsimp only [t] at hb; unfold cyclicOffset at hb; linear_combination hb
    have hgap : (b-p b).val=1 := by
      have he : b-p b=(1 : Fin n) := by linear_combination -hraw
      rw [he,hv1]
    exact False.elim (even_unpaid_small_gap_not_minimum p a b hn hh hmin hunpaid (by omega) (by omega) hheight)
  obtain ⟨b,hb,hheight⟩ := hex
  have hraw : p b-b= -2 := by dsimp only [t] at hb; unfold cyclicOffset at hb; linear_combination hb
  have hgap : (b-p b).val=2 := by
    have he : b-p b=(2 : Fin n) := by linear_combination -hraw
    rw [he,hv2]
  have hf := (even_unpaid_binary_height_profile p a hn hh hmin hunpaid).2.1 b hheight
  have hor : b.val < (p b).val ∨ p b=0 := by
    by_cases hz : p b=0
    · exact Or.inr hz
    apply Or.inl
    by_contra hnot
    have hne : p b ≠ b := by intro he; rw [he,sub_self,Fin.val_zero] at hgap; omega
    have hvne : (p b).val ≠ b.val := fun he => hne (Fin.ext he)
    have hd : b ∈ descendingPositions p := (mem_descendingPositions _ _).mpr (by omega)
    have hlow := even_unpaid_positive_backward_minimum p a hn hh hmin hunpaid b hd hz
    omega
  have hfinish : b.val+(-p b).val=2 := by
    rcases hor with hforward | hz
    · have hpne : p b ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
      have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hpne]
      rw [Fin.coe_sub_iff_lt.mpr (show b < p b from hforward)] at hgap
      rw [hneg]
      have := (p b).isLt
      omega
    · simpa only [hz,neg_zero,Fin.val_zero,add_zero,sub_zero] using hgap
  refine ⟨b,hheight,hraw,hf,hor,hfinish,?_⟩
  intro i hi
  have hif : i ∈ fixedPositions (permutation p b) := by
    rw [mem_fixedPositions]
    change p i+(b-p b)=i
    linear_combination hi
  have hbf : b ∈ fixedPositions (permutation p b) := (mem_fixedPositions _ _).mpr (permutation_anchor p b)
  have he : i=b := Finset.card_le_one.mp hf.le i hif b hbf
  rw [he]

#print axioms even_unpaid_terminal_two
end LX.AnchoredPhases
