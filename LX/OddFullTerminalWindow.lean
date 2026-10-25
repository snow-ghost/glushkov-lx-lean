import LX.MinimumHeadObstruction
import LX.MinimumSmallGap
import LX.OddPairedHigherPayment
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The whole terminal half-window is covered without discarding a
rank-dependent initial segment. Only the head, its predecessor, and one
aligned phase are exceptional. -/
theorem odd_full_terminal_threshold (p : State n) (a z : Fin n) (g : ℕ)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9)
    (hz : ∀ b,HigherAlignedTerminal p (height p a) b → p b-b=p z-z)
    (hg1 : 1 ≤ g) (hg2 : g ≤ height p a+3) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      -(g : Fin n)=p 0 ∨ (-(g : Fin n)=p 0-1 ∧ height p 0=height p a) ∨
      (-(g : Fin n)=p z-z ∧ ∃ b,HigherAlignedTerminal p (height p a) b) ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ p c ≠ 0 ∧
        height p c=height p a+1 ∧ p c-c= -(g : Fin n) := by
  let t : Fin n := -(g : Fin n)-(p a-a)
  have hgn : g < n := by omega
  have hgv : (g : Fin n).val=g := Nat.mod_eq_of_lt hgn
  by_cases hhigh : 2 ≤ rankSurplus p a t.val
  · exact Or.inl hhigh
  have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
  by_cases hzero : rankSurplus p a t.val=0
  · obtain ⟨b,hb,hheight⟩ := zero_surplus_anchor p a hmin t hzero
    have hraw : p b-b= -(g : Fin n) := by
      dsimp only [t] at hb
      unfold cyclicOffset at hb
      linear_combination hb
    have hgap : (b-p b).val=g := by
      have he : b-p b=(g : Fin n) := by linear_combination -hraw
      rw [he,hgv]
    have hhead : p 0=p b-b := by
      by_contra hnot
      have hh := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hheight hnot hunpaid
      omega
    exact Or.inr (Or.inl (hraw.symm.trans hhead.symm))
  have hone : rankSurplus p a t.val=1 := by omega
  rcases rank_one_occupied_or_next_minimum p a t hmin hone with
    ⟨b,hb,hheight⟩ | ⟨b,hb,hheight⟩
  · have hraw : p b-b= -(g : Fin n) := by
      dsimp only [t] at hb
      unfold cyclicOffset at hb
      linear_combination hb
    obtain ⟨c,hcb,hch,_,hlast⟩ := last_offset_source p b
    have hcr : p c-c= -(g : Fin n) := hcb.trans hraw
    have hc : height p c=height p a+1 := hch.trans hheight
    have hgap : (c-p c).val=g := by
      have he : c-p c=(g : Fin n) := by linear_combination -hcr
      rw [he,hgv]
    by_cases hhead : p 0=p c-c
    · exact Or.inr (Or.inl (hcr.symm.trans hhead.symm))
    by_cases hd : (p c).val < c.val ∧ p c ≠ 0
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨c,(mem_descendingPositions _ _).mpr hd.1,hd.2,hc,hcr⟩)))
    have hfinish : c.val+(-p c).val=(c-p c).val := by
      by_cases hp0 : p c=0
      · simp [hp0]
      have hne : p c ≠ c := by intro he; rw [he,sub_self,Fin.val_zero] at hgap; omega
      have hvne : (p c).val ≠ c.val := fun he => hne (Fin.ext he)
      have hforward : c.val < (p c).val := by omega
      have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hp0]
      rw [hneg,Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)]
      have := (p c).isLt
      omega
    have hexc : HigherAlignedTerminal p (height p a) c := ⟨hc,hhead,hlast,hfinish,by omega,by omega⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcr.symm.trans (hz c hexc),c,hexc⟩)))
  · have hraw : p b-b= -((g-1 : ℕ) : Fin n) := by
      dsimp only [t] at hb
      unfold cyclicOffset at hb
      rw [Nat.cast_sub hg1,Nat.cast_one]
      linear_combination hb
    have hgap : (b-p b).val=g-1 := by
      have he : b-p b=((g-1 : ℕ) : Fin n) := by linear_combination -hraw
      rw [he]
      exact Nat.mod_eq_of_lt (by omega)
    have hhead : p 0=p b-b := by
      by_contra hnot
      have hh := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hheight hnot hunpaid
      omega
    apply Or.inr
    apply Or.inr
    apply Or.inl
    constructor
    · rw [hhead,hraw,Nat.cast_sub hg1,Nat.cast_one]
      ring
    · exact (equal_raw_offset_height p 0 b (by simpa using hhead)).trans hheight

#print axioms odd_full_terminal_threshold
end LX.AnchoredPhases
