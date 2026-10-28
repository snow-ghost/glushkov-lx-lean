import LX.ConjecturePhaseReduction
import LX.ConjectureTerminalWindow
import LX.LowForwardPayment
import LX.MinimumGapPhases
import LX.RankPeakReserve
import LX.SecondExcess
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 500000 in
/-- Necessary conditions for a counterexample to the conjectured parity bounds.
This is a reduction, not an assertion that those conditions are impossible. -/
theorem conjecture_unpaid_rank_geometry (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∃ a r : Fin n,∃ R : ℕ,6 < n ∧ GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ b,height p a ≤ height p b) ∧ 0 < R ∧ R+2*e ≤ 8 ∧
      rankSurplus p a r.val=R ∧ (∀ t : Fin n,rankSurplus p a t.val ≤ R) ∧
      secondExcess p a ≤ (2*(R : ℤ)+1+(R+2-(e*m+3) : ℕ)) := by
  classical
  have hnlarge : 6 < n := by
    by_contra hnot
    exact hunpaid (conjecture_small_word hn4 (by omega) p m e he hn)
  obtain ⟨a,ha,hh,hmin⟩ := conjecture_unpaid_minimum hn4 p m e he hn hunpaid
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun t => rankSurplus p a t.val) ⟨0,Finset.mem_univ _⟩
  have hr0 := rank_surplus_nonnegative p a hmin r.val (Nat.le_of_lt r.isLt)
  let R := (rankSurplus p a r.val).toNat
  have hpeak : rankSurplus p a r.val=R := by dsimp [R]; rw [Int.toNat_of_nonneg hr0]
  have hR (t : Fin n) : rankSurplus p a t.val ≤ R := by
    rw [← hpeak]
    exact hr t (Finset.mem_univ _)
  have hRpos : 0 < R := by
    by_contra hnot
    have hz (t : Fin n) : rankSurplus p a t.val=0 := by
      have hi := hR t
      have hlo := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
      omega
    have hs := rank_surplus_sum p a
    simp_rw [hz] at hs
    simp only [Finset.sum_const_zero,mul_zero] at hs
    interval_cases e <;>
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 ∨ (n : ℤ)=2*(height p a : ℤ)+3 := by omega
    all_goals rcases hn' with hn' | hn' <;> nlinarith
  have hb := rank_peak_anchor_bounds p a R hmin hR
  obtain ⟨z,hz⟩ := exists_least_gap_above p m (R+1)
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  have hquad : ((R : ℤ)-1)*(R-2) ≤ 2*(Z.card : ℤ)-2*(P.card : ℤ)+
      (n : ℤ)*((n : ℤ)-3-2*height p a) :=
    minimum_count_minus_high_count p a r R hmin hRpos hpeak
  let Dlow := (descendingPositions p).filter fun b => height p b=height p a
  let Dhigh := (descendingPositions p).filter fun b => height p b=m
  obtain ⟨b,hbmem,hbgap⟩ := Finset.exists_min_image
    (Finset.univ.filter fun b : Fin n => height p b=height p a) (fun b => (b-p b).val)
    ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hbh : height p b=height p a := (Finset.mem_filter.mp hbmem).2
  obtain ⟨v,hv⟩ := exists_least_gap_above p (height p a) (R+2)
  let E := ({(b-p b).val} ∪ {(v-p v).val}) ∪ Finset.Ico (e*m+3) (R+2)
  have hE : E.card ≤ 2+(R+2-(e*m+3)) := by
    have hc : E.card ≤ (({(b-p b).val} ∪ {(v-p v).val}) : Finset ℕ).card+
        (Finset.Ico (e*m+3) (R+2)).card := Finset.card_union_le _ _
    have hp := Finset.card_union_le {(b-p b).val} {(v-p v).val}
    simp only [Finset.card_singleton,Nat.card_Ico] at hc hp
    omega
  let Hlow : ℕ := if height p 0=height p a then 1 else 0
  let Hhigh : ℕ := if height p 0=m then 1 else 0
  have hheads : Hlow+Hhigh ≤ 1 := by
    dsimp [Hlow,Hhigh]
    split_ifs <;> omega
  have hlow : Z.card ≤ Dlow.card+E.card+Hlow := by
    have hc := low_offset_count_of_forward_payment p (height p a) E hunpaid (by
      intro c hch hgap hhead hlast hback
      by_cases hsmall : (c-p c).val < e*m+3
      · have hle := hbgap c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hch⟩)
        have hne : (c-p c).val ≠ (b-p b).val := by
          intro heq
          apply hgap
          simp [E,heq]
        have hf := smaller_gap_bounds_fixed p c b (by omega) (by omega)
        have hr := anchor_reserve_nonneg p c
        interval_cases e
        · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
        · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
      · have hglow : R+2 ≤ (c-p c).val := by
          by_contra hnot
          exact hgap (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
        have hv' := hv c hch hglow
        have hne : (c-p c).val ≠ (v-p v).val := by
          intro heq
          apply hgap
          simp [E,heq]
        have hf := gap_separation_bounds_fixed p c v (by omega) (by omega)
        have hd := rank_peak_next_depth_fiber p a R hR c (by omega)
        obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega)
          (by interval_cases e <;> omega) hhead hlast hback (by omega) (by omega)
        exact ⟨w,hw,by omega⟩)
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    exact hc
  have hupper : e*m+2 < n := by interval_cases e <;> omega
  let I := Finset.Icc (R+1) (e*m+2)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  have hWcard : W.card=I.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj he
    have hi' := (Finset.mem_Icc.mp hi).2
    have hj' := (Finset.mem_Icc.mp hj).2
    have hij : (i : Fin n)=(j : Fin n) := neg_injective he
    have hiv : (i : Fin n).val=i := Nat.mod_eq_of_lt (by omega)
    have hjv : (j : Fin n).val=j := Nat.mod_eq_of_lt (by omega)
    have hv := congrArg Fin.val hij
    omega
  have hWlower : (e*m : ℕ)+2-(R : ℤ) ≤ W.card := by
    rw [hWcard]
    dsimp only [I]
    rw [Nat.card_Icc]
    omega
  let Bad := P.image (fun t => p a-a+t)
  let V := Dhigh.image (fun b => p b-b)
  have hBad : Bad.card ≤ P.card := Finset.card_image_le
  have hV : V.card ≤ Dhigh.card := Finset.card_image_le
  let Head : Finset (Fin n) := if height p 0=m then {p 0} else ∅
  have hHead : Head.card=Hhigh := by dsimp [Head,Hhigh]; split_ifs <;> simp
  have hsub : W ⊆ (Bad ∪ Head) ∪ (V ∪ {p z-z}) := by
    intro t ht
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    have hg' := Finset.mem_Icc.mp hg
    have ht := conjecture_window_terminal_threshold p a z m R g e he hn hnlarge hupper hh hmin hb.2 hR hz hunpaid
      hg'.1 hg'.2
    rcases ht with hhigh | hhead | hspecial | ⟨b,hb,hbh,hbr⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
      ring
    · apply Finset.mem_union_left
      simp [Head,hhead.1,hhead.2]
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_singleton.mpr hspecial
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,hbh⟩,hbr⟩
  have hwindow : W.card ≤ P.card+Hhigh+1+Dhigh.card := by
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ Head) (V ∪ {p z-z}))
    have hB := Finset.card_union_le Bad Head
    rw [hHead] at hB
    have hVextra := Finset.card_union_le V {p z-z}
    simp only [Finset.card_singleton] at hVextra
    omega
  have hdisjoint : Disjoint Dlow Dhigh := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    omega
  have hsubset : Dlow ∪ Dhigh ⊆ descendingPositions p := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hb).1
  have hsum := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint] at hsum
  have hdesc := rank_peak_descending_count p a R hR
  have hlinear : (Z.card : ℤ)-(P.card : ℤ) ≤
      (m : ℤ)-(e*m : ℕ)+2*(R : ℤ)+(E.card : ℤ)-1 := by omega
  have hquad' : ((R : ℤ)-1)*(R-2) ≤ 4*(R : ℤ)+2*E.card-2 := by
    interval_cases e
    · simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith only [hquad,hlinear,hn',hm']
    · simp only [Nat.one_mul] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hquad,hlinear,hn']
  have hheight : (height p a : ℤ)+R ≤ (n : ℤ)-1 := by
    have hm := shifted_offset_rank_mass p a r
    have hs : (∑ i : Fin n,((cyclicOffset p a i-r : Fin n) : ℤ)) ≤
        (n : ℤ)*((n : ℤ)-1) := by
      calc
        _ ≤ ∑ _i : Fin n,((n : ℤ)-1) := by
          apply Finset.sum_le_sum
          intro i _
          have := (cyclicOffset p a i-r).isLt
          omega
        _ = _ := by simp; ring
    rw [hm,hpeak] at hs
    have hnpos : (0 : ℤ) < n := by omega
    nlinarith only [hs,hnpos]
  have hRbound : R+e ≤ 8 := by
    interval_cases e
    · simp only [Nat.zero_mul] at hE
      have hE' : (E.card : ℤ) ≤ (R : ℤ)+1 := by omega
      by_contra hnot
      have hr : (9 : ℤ) ≤ R := by omega
      nlinarith only [hquad',hE',hr,mul_nonneg (by omega : (0 : ℤ) ≤ R)
        (by omega : (0 : ℤ) ≤ (R : ℤ)-9)]
    · simp only [Nat.one_mul] at hE
      have hE' : (E.card : ℤ) ≤ 2 := by omega
      by_contra hnot
      have hr : (8 : ℤ) ≤ R := by omega
      nlinarith only [hquad',hE',hr,mul_nonneg (by omega : (0 : ℤ) ≤ R)
        (by omega : (0 : ℤ) ≤ (R : ℤ)-7)]
  have hQ : secondExcess p a ≤ (2*(R : ℤ)+1+(R+2-(e*m+3) : ℕ)) := by
    have hc := second_excess_count p a hmin
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+
      (n : ℤ)*((n : ℤ)-3-2*height p a) at hc
    have hE' : (E.card : ℤ) ≤ 2+((R+2-(e*m+3) : ℕ) : ℤ) := by exact_mod_cast hE
    interval_cases e
    · simp only [Nat.zero_mul,Nat.cast_zero,sub_zero] at hlinear hE' ⊢
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith only [hc,hlinear,hE',hn',hm']
    · simp only [Nat.one_mul] at hlinear hE' ⊢
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hc,hlinear,hE',hn']
  have hRbound' : R+2*e ≤ 8 := by
    interval_cases e
    · omega
    · by_contra hnot
      have hseven : R=7 := by omega
      have hres := critical_rank_peak_reserve p a r ha 1 (by omega)
      rw [hpeak,hseven] at hres
      norm_num at hres
      have hmlarge : 36 ≤ m := by
        by_contra hsmall
        obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
          p (phase p a) (displacement p a) (is_lift p a) (global_minimum_majorized ha)
          (height p a) (by omega) (by omega)
          (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
        apply hunpaid
        refine ⟨w,hw,?_⟩
        norm_num
        have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
        have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
        have hm35 : (m : ℤ) ≤ 35 := by omega
        unfold anchorReserve at hres
        nlinarith only [hprice,hres,hn',hm',hm35]
      have hlow' : Z.card ≤ Dlow.card+1+Hlow := by
        have hc := low_offset_count_of_forward_payment p (height p a) {(b-p b).val} hunpaid (by
          intro c hch hgap hhead hlast hback
          have hne : (c-p c).val ≠ (b-p b).val := by simpa using hgap
          have hle := hbgap c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hch⟩)
          by_cases hsmall : (c-p c).val < m+3
          · have hf := smaller_gap_bounds_fixed p c b (by omega) (by omega)
            have hr := anchor_reserve_nonneg p c
            obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p c (by omega) (by omega) (by omega)
            exact ⟨w,hw,by norm_num; omega⟩
          · have hd := rank_peak_next_depth p a R hR c (by omega)
            obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega)
              (Or.inr (by omega)) hhead hlast hback (by omega) (by omega)
            exact ⟨w,hw,by norm_num; omega⟩)
        rw [← zero_surplus_count_eq_minimum_offsets p a hmin,Finset.card_singleton] at hc
        exact hc
      have hlinear' : (Z.card : ℤ)-(P.card : ℤ) ≤ 14 := by
        simp only [Nat.one_mul] at hWlower
        omega
      rw [hseven] at hquad
      norm_num at hquad
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith only [hquad,hlinear',hn']
  exact ⟨a,r,R,hnlarge,ha,hh,hmin,hRpos,hRbound',hpeak,hR,hQ⟩

#print axioms conjecture_unpaid_rank_geometry
end LX.AnchoredPhases
