import LX.EvenTerminalWindow
import LX.NearTopPrefixBound
import LX.OddTerminalWindow
import LX.PrefixGapDeadline
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- A last minimum-height representative whose literal finishing cursor
equals its cyclic gap has the conjectured price for both parities. -/
theorem gap_aligned_minimum_conjecture_word (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e)
    (hh : 2 ≤ height p a) (hmin : ∀ b,height p a ≤ height p b)
    (hfinish : a.val+(-p a).val=(a-p a).val) (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hf : (fixedPositions (permutation p a)).card ≤ (a-p a).val+1 := by
    have hs : fixedPositions (permutation p a) ⊆ Finset.Iic a := by
      intro i hi
      apply Finset.mem_Iic.mpr
      apply hlast i
      have hpi := (mem_fixedPositions _ _).mp hi
      change p i+(a-p a)=i at hpi
      linear_combination hpi
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    omega
  by_cases hsmall : ((a-p a).val : ℤ)-anchorReserve p a ≤ 2+(e : ℤ)*((height p a : ℤ)+1)
  · interval_cases e
    · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p a (by omega) (by omega) hf
      norm_num at hsmall ⊢
      exact ⟨w,hw,by omega⟩
    · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p a (by omega) (by omega) hf
      norm_num at hsmall ⊢
      exact ⟨w,hw,by omega⟩
  have hhead' : permutation p a 0 ≠ 0 := by
    intro heq
    apply hhead
    change p 0+(a-p a)=0 at heq
    linear_combination heq
  obtain ⟨i,hi,hbound⟩ := minimum_height_early_low_depth p a hmin hh hhead'
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  have hifinish : i.val ≤ a.val+(-p a).val := by
    rw [hfinish]
    interval_cases e <;> norm_num at hsmall hn' <;> omega
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p a hh (by omega)
    hhead hlast i hi hifinish
  have hfin : (a.val : ℤ)+((-p a).val : ℤ)=((a-p a).val : ℤ) := by exact_mod_cast hfinish
  have hgap : ((a-p a).val : ℤ) < n := by exact_mod_cast (a-p a).isLt
  have hreserve := anchor_reserve_nonneg p a
  unfold anchorReserve at hreserve
  refine ⟨w,hw,?_⟩
  interval_cases e <;> norm_num at hn' ⊢ <;>
    nlinarith only [hprice,hfin,hgap,hreserve,hn']

/-- Forward last representatives satisfy the literal finishing condition. -/
theorem forward_minimum_conjecture_word (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e)
    (hh : 2 ≤ height p a) (hmin : ∀ b,height p a ≤ height p b)
    (hforward : a.val < (p a).val) (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hpne : p a ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
  have hneg : (-p a).val=n-(p a).val := by simp [Fin.val_neg,hpne]
  have hgapval : (a-p a).val=n+a.val-(p a).val :=
    Fin.coe_sub_iff_lt.mpr (show a < p a from hforward)
  apply gap_aligned_minimum_conjecture_word p a e he hn hh hmin ?_ hhead hlast
  rw [hneg,hgapval]
  have := (p a).isLt
  omega

/-- A last representative mapping to zero has the same inexpensive finish. -/
theorem zero_image_minimum_conjecture_word (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e)
    (hh : 2 ≤ height p a) (hmin : ∀ b,height p a ≤ height p b)
    (hzero : p a=0) (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e :=
  gap_aligned_minimum_conjecture_word p a e he hn hh hmin (by simp [hzero]) hhead hlast

#print axioms gap_aligned_minimum_conjecture_word
#print axioms forward_minimum_conjecture_word
#print axioms zero_image_minimum_conjecture_word
end LX.AnchoredPhases
