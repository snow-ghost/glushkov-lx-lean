import LX.RankWindowPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 500000 in
/-- A common terminal interval pays both parities with constant 32.
The first count bounds the peak by ten; prefix words then sharpen the
second count. Small odd sizes use the selected lower-height phase. -/
theorem rank_window_quadratic_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  classical
  by_contra hunpaid
  have hunpaid32 : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by linarith⟩
  have hnlarge : 21 < n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ) ≤ 21 := by omega
    linarith
  obtain ⟨a,ha,hh⟩ : ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m := by
    interval_cases e
    · obtain ⟨a,ha⟩ := exists_global_minimum p
      exact ⟨a,ha,even_unpaid_global_height hn4 m (by omega) ha hunpaid32⟩
    · exact odd_unpaid_lower_global_minimum hn4 p m hn hunpaid32
  have hmin (b : Fin n) : height p a ≤ height p b := by
    interval_cases e
    · exact even_unpaid_global_minimum_height p m (by omega) hn4 hunpaid32 a ha b
    · by_contra hnot
      obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
      exact hunpaid32 ⟨w,hw,by linarith⟩
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
  have hdepth (b : Fin n) (hbHeight : height p b=m) :
      depthCount (displacement p b) (height p b-1) ≤ 2*R+1 := by
    have hc := rank_peak_next_depth p a R hR b (by omega)
    omega
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  have hquad : ((R : ℤ)-1)*(R-2) ≤ 2*(Z.card : ℤ)-2*(P.card : ℤ)+
      (n : ℤ)*((n : ℤ)-3-2*height p a) :=
    minimum_count_minus_high_count p a r R hmin hRpos hpeak
  let Dlow := (descendingPositions p).filter fun b => height p b=height p a
  let Dhigh := (descendingPositions p).filter fun b => height p b=m
  have hlow : Z.card ≤ Dlow.card+2*R+4 := by
    have hc := rank_window_low_offset_count p a R (2*R+3) hR (by omega)
      (by interval_cases e <;> omega) hunpaid (by intros; omega)
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    change Z.card ≤ Dlow.card+(2*R+3)+1 at hc
    omega
  have hupper : e*m+16 < n := by
    interval_cases e
    · omega
    · by_contra hnot
      obtain ⟨w,hw,hprice⟩ := candidate_head_reserve_word (by omega : 2 ≤ n) p a (by omega)
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      have hm' : (height p a : ℤ) ≤ 14 := by omega
      exact hunpaid ⟨w,hw,by nlinarith⟩
  let I := Finset.Icc (2*R+1) (e*m+16)
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
  have hWlower : (e*m : ℕ)+16-2*(R : ℤ) ≤ W.card := by
    rw [hWcard]
    dsimp only [I]
    rw [Nat.card_Icc]
    omega
  let Bad := P.image (fun t => p a-a+t)
  let V := Dhigh.image (fun b => p b-b)
  have hBad : Bad.card ≤ P.card := Finset.card_image_le
  have hV : V.card ≤ Dhigh.card := Finset.card_image_le
  have hsub : W ⊆ (Bad ∪ {p 0}) ∪ V := by
    intro t ht
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ht
    have hg' := Finset.mem_Icc.mp hg
    have ht := rank_window_terminal_threshold p a m R g e he hn hnlarge hupper hh hmin hb.2 hdepth hunpaid
      hg'.1 hg'.2
    rcases ht with hhigh | hhead | ⟨b,hb,hbh,hbr⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
      ring
    · apply Finset.mem_union_left
      simp [hhead]
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,hbh⟩,hbr⟩
  have hwindow : W.card ≤ P.card+1+Dhigh.card := by
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ {p 0}) V)
    have hB := Finset.card_union_le Bad {p 0}
    simp only [Finset.card_singleton] at hB
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
  have hlinear : (Z.card : ℤ)-(P.card : ℤ) ≤ (m : ℤ)-(e*m : ℕ)+5*(R : ℤ)-12 := by
    omega
  have hRquad : (R : ℤ)^2-13*R+26 ≤ 0 := by
    interval_cases e
    · simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith
    · simp only [Nat.one_mul] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith
  have hRten : R ≤ 10 := by
    by_contra hnot
    have hp := mul_nonneg (show 0 ≤ (R : ℤ)-11 by omega) (show 0 ≤ (R : ℤ)-2 by omega)
    nlinarith
  have hlow' : Z.card ≤ Dlow.card+R+1 := by
    have hc := rank_window_low_offset_count p a R R hR (by omega)
      (by interval_cases e <;> omega) hunpaid (by
        intro b hbh hglo hghi
        have hf := hb.2 b
        have hr := anchor_reserve_nonneg p b
        interval_cases e
        · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
        · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩)
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    exact hc
  have hlinear' : (Z.card : ℤ)-(P.card : ℤ) ≤ (m : ℤ)-(e*m : ℕ)+4*(R : ℤ)-15 := by
    omega
  have hsquare := sq_nonneg (2*(R : ℤ)-11)
  interval_cases e
  · simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hlinear'
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
    have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
    nlinarith
  · simp only [Nat.one_mul] at hlinear'
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
    nlinarith

#print axioms rank_window_quadratic_upper_word
end LX.AnchoredPhases
