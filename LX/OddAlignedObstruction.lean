import LX.FiberDepthGeometry
import LX.OddPairedHigherPayment
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- An unpaid aligned terminal phase has no low-depth position before
its finish; otherwise the existing literal scan already pays it. -/
theorem odd_unpaid_aligned_prefix (p : State n) (h : ℕ) (b : Fin n)
    (hn : n=2*h+3) (hh : 1 ≤ h) (hb : HigherAlignedTerminal p h b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∀ i : Fin n,i.val ≤ (b-p b).val →
      height p b-1 ≤ backwardDepth (displacement p b) i := by
  intro i hi
  obtain ⟨hheight,hhead,hlast,hfinish,_,hgap⟩ := hb
  by_contra hnot
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p b (by omega) (by omega)
    hhead hlast i (by omega) (by omega)
  have hcap := (candidate_price_components p b).1
  have hn' : (n : ℤ)=2*(height p b : ℤ)+1 := by omega
  have hfin : (b.val : ℤ)+((-p b).val : ℤ)=((b-p b).val : ℤ) := by exact_mod_cast hfinish
  have hg : ((b-p b).val : ℤ) ≤ (height p b : ℤ)+2 := by omega
  exact hunpaid ⟨w,hw,by nlinarith only [hprice,hcap,hn',hfin,hg]⟩

/-- In the last odd rank profile an unpaid aligned phase finishes within
four positions. Its head image is within three normalized positions. -/
theorem rank_two_unpaid_aligned_gap (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    let F := (fixedPositions (permutation p b)).card
    1 ≤ F ∧ F ≤ 2 ∧ F ≤ (b-p b).val ∧
      (b-p b).val ≤ F+2 ∧
      1 ≤ (cyclicOffset p b 0).val ∧ (cyclicOffset p b 0).val ≤ F+1 := by
  classical
  let F := (fixedPositions (permutation p b)).card
  have hheight := hb.1
  have hhead := hb.2.1
  have hlast := hb.2.2.1
  have hfinish := hb.2.2.2.1
  have hpre := odd_unpaid_aligned_prefix p (height p a) b hn (by omega) hb hunpaid
  have hFpos : 1 ≤ F := Finset.card_pos.mpr ⟨b,(mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
  have hFcap := rank_peak_fixed_count p a 2 hR b
  have hFtwo : F ≤ 2 := by change (F : ℤ)+height p b ≤ _ at hFcap; omega
  have hq0 : permutation p b 0 ≠ 0 := by
    intro he
    apply hhead
    change p 0+(b-p b)=0 at he
    linear_combination he
  have hsubF : fixedPositions (permutation p b) ⊆ Finset.Ioc (0 : Fin n) b := by
    intro i hi
    have hfix := (mem_fixedPositions _ _).mp hi
    have hi0 : i ≠ 0 := by intro he; subst i; exact hq0 hfix
    have hraw : p i-i=p b-b := by
      change p i+(b-p b)=i at hfix
      linear_combination hfix
    exact Finset.mem_Ioc.mpr ⟨Fin.pos_iff_ne_zero.mpr hi0,hlast i hraw⟩
  have hFgap : F ≤ (b-p b).val := by
    have hc := Finset.card_le_card hsubF
    rw [Fin.card_Ioc,Fin.val_zero,Nat.sub_zero] at hc
    change F ≤ b.val at hc
    omega
  have hsub : Finset.Iic (b-p b) ⊆
      Finset.univ.filter (fun i : Fin n => height p b-1 ≤ backwardDepth (displacement p b) i) := by
    intro i hi
    have hi' := Finset.mem_Iic.mp hi
    change i.val ≤ (b-p b).val at hi'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpre i hi'⟩
  have hcnt := Finset.card_le_card hsub
  rw [Fin.card_Iic] at hcnt
  change (b-p b).val+1 ≤ depthCount (displacement p b) (height p b-1) at hcnt
  have hdepth := rank_peak_next_depth_fiber p a 2 hR b (by omega)
  change (depthCount (displacement p b) (height p b-1) : ℤ)+height p b ≤
    (height p a : ℤ)+2+F+2 at hdepth
  have hheadpre := hpre 0 (by simp)
  have hw := displacement_depth_width_bound (is_lift p b)
    (fun i j => (displacement_strict_width p b i j).le) (height p b-1) 0 hheadpre
  rw [show height p b-1+1=height p b by omega,displacement_offset,top_depth_count_eq_fixed] at hw
  change ((cyclicOffset p b 0).val : ℤ)-height p b+
    (backwardDepth (displacement p b) 0 : ℤ) ≤ F at hw
  have hoff0 : cyclicOffset p b 0 ≠ 0 := by
    intro he
    exact hq0 ((offset_zero_iff_source_fixed p b 0).mp he)
  have hoffpos : 0 < (cyclicOffset p b 0).val := Fin.pos_iff_ne_zero.mpr hoff0
  change 1 ≤ F ∧ F ≤ 2 ∧ F ≤ (b-p b).val ∧
      (b-p b).val ≤ F+2 ∧ 1 ≤ (cyclicOffset p b 0).val ∧ (cyclicOffset p b 0).val ≤ F+1
  omega

theorem rank_two_unpaid_aligned_head_range (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ j : ℤ,-3 ≤ j ∧ j ≤ 1 ∧ p 0=(j : Fin n) := by
  obtain ⟨hFpos,hFtwo,hFgap,hgap,hoffpos,hoffcap⟩ := rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  let j : ℤ:=((cyclicOffset p b 0).val : ℤ)-((b-p b).val : ℤ)
  refine ⟨j,by dsimp [j]; omega,by dsimp [j]; omega,?_⟩
  have he : cyclicOffset p b 0-(b-p b)=p 0 := by unfold cyclicOffset; ring
  simpa only [j,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self] using he.symm

#print axioms odd_unpaid_aligned_prefix
#print axioms rank_two_unpaid_aligned_gap
#print axioms rank_two_unpaid_aligned_head_range
end LX.AnchoredPhases
