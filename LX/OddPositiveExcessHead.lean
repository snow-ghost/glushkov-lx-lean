import LX.OddHeadTerminalExcess
import LX.ReverseDualPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem odd_unpaid_positive_excess_head_fixed (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hpos : 0 < secondExcess p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 := by
  have hb := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  have hK : HeadPredecessorTerminal p (height p a) := by
    by_contra hnot
    rw [ite_eq_right hnot] at hb
    split_ifs at hb <;> omega
  obtain ⟨hhead,hg1,hg2⟩ := hK
  by_contra hp0
  have hgp : 0 < (-p 0).val := Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hp0)
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hv := Fin.val_add_eq_ite (-p 0) (1 : Fin n)
  have he : -p 0+1=(1 : Fin n)-p 0 := by ring
  rw [he,hv1] at hv
  have hgn := (-p 0).isLt
  have hg : (-p 0).val ≤ height p a+3 := by split_ifs at hv <;> omega
  have hz := odd_unpaid_terminal_head_zero_excess p a hn hh hmin hR hhead hgp hg hunpaid
  omega

/-- Applying the same count to the reflected inverse fixes both initial
positions whenever a positive second excess remains. -/
theorem odd_unpaid_positive_excess_initial_pair (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hpos : 0 < secondExcess p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 ∧ p 1=1 := by
  have hp0 := odd_unpaid_positive_excess_head_fixed p a hn hh hmin hR hpos hunpaid
  have hdual : ¬ ∃ w : List Letter,reverseDual p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w.reverse,reverse_dual_sorting_word p w hw,by simpa using hprice⟩
  have hheight := reverse_dual_height p a
  have hq0 := odd_unpaid_positive_excess_head_fixed (reverseDual p) (dualPosition p a)
    (by omega) (by omega) (reverse_dual_minimum_height p a hmin)
    (fun t => by rw [reverse_dual_rank_surplus]; exact hR t)
    (by rw [reverse_dual_second_excess]; exact hpos) hdual
  have he : (1 : Fin n)-p.symm 1=0 := by
    simpa only [reverseDual,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      LX.Core.WordReflection.reflection_apply,sub_zero] using hq0
  have hi : p.symm 1=1 := by linear_combination -he
  refine ⟨hp0,?_⟩
  have hp1 := p.apply_symm_apply 1
  rwa [hi] at hp1

theorem odd_fixed_initial_pair_no_aligned_terminal (p : State n) (h : ℕ)
    (hn : n=2*h+3) (hh : 1 ≤ h) (hp0 : p 0=0) (hp1 : p 1=1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ¬∃ b,HigherAlignedTerminal p h b := by
  rintro ⟨b,hbh,hhead,hlast,hfinish,hgpos,hgupper⟩
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hb0 : b ≠ 0 := by intro he; apply hhead; simp [he]
  have hgaplarge : 2 ≤ (b-p b).val := by
    by_contra hnot
    have hbpos : 0 < b.val := Fin.pos_iff_ne_zero.mpr hb0
    have hb1 : b=1 := Fin.ext (by omega)
    rw [hb1,hp1,sub_self,Fin.val_zero] at hgpos
    omega
  have hq0 : permutation p b 0=b-p b := by change p 0+(b-p b)=b-p b; rw [hp0,zero_add]
  have hlow : backwardDepth (displacement p b) 0 < height p b-1 := by
    by_contra hnot
    have hmax : backwardDepth (displacement p b) 0 ≤ height p b := by
      exact_mod_cast (candidate_price_components p b).2 0
    have hne : backwardDepth (displacement p b) 0 ≠ height p b := by
      intro he
      have hfix := (depth_eq_height_iff_fixed p b 0).mp he
      rw [hq0] at hfix
      rw [hfix,Fin.val_zero] at hgpos
      omega
    have hnear : backwardDepth (displacement p b) 0=height p b-1 := by omega
    have hfix1 := (near_top_open_arc_fixed p b 0 (by omega) hnear).2 (1 : Fin n)
      (by simp only [sub_zero,hv1]; omega)
      (by simp only [sub_zero,hq0,hv1]; omega)
    change p 1+(b-p b)=1 at hfix1
    rw [hp1] at hfix1
    have hz : b-p b=0 := by linear_combination hfix1
    rw [hz,Fin.val_zero] at hgpos
    omega
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p b (by omega) (by omega)
    hhead hlast 0 hlow (by simp)
  have hcap := (candidate_price_components p b).1
  have hn' : (n : ℤ)=2*(height p b : ℤ)+1 := by omega
  have hfin : (b.val : ℤ)+((-p b).val : ℤ)=((b-p b).val : ℤ) := by exact_mod_cast hfinish
  have hg : ((b-p b).val : ℤ) ≤ (height p b : ℤ)+2 := by omega
  exact hunpaid ⟨w,hw,by nlinarith only [hprice,hcap,hn',hfin,hg]⟩

/-- Positive second excess is impossible: it fixes the initial pair,
which removes the aligned exception required by the exact window count. -/
theorem odd_unpaid_second_excess_zero (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : secondExcess p a=0 := by
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  by_contra hnot
  have hpos : 0 < secondExcess p a := by omega
  obtain ⟨hp0,hp1⟩ := odd_unpaid_positive_excess_initial_pair p a hn hh hmin hR hpos hunpaid
  have hnone := odd_fixed_initial_pair_no_aligned_terminal p (height p a) hn (by omega) hp0 hp1 hunpaid
  have hb := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  rw [ite_eq_right hnone] at hb
  split_ifs at hb <;> omega

#print axioms odd_unpaid_positive_excess_initial_pair
#print axioms odd_fixed_initial_pair_no_aligned_terminal
#print axioms odd_unpaid_second_excess_zero
end LX.AnchoredPhases
