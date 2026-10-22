import LX.ShortWindowPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 500000 in
/-- The full rank profile and two explicit exception intervals give a
uniform bound with constant eighteen, including all small dimensions. -/
theorem short_window_quadratic_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*18 := by
  classical
  by_contra hunpaid
  have hnlarge : 12 < n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ) ≤ 12 := by omega
    linarith
  obtain ⟨a,ha,hh,hmin⟩ := eighteen_unpaid_minimum hn4 p m e he hn hunpaid
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
  let E := Finset.range R ∪ Finset.Ico 17 (2*R+3)
  have hE : E.card ≤ R+(2*R+3-17) := by
    have hc := Finset.card_union_le (Finset.range R) (Finset.Ico 17 (2*R+3))
    simpa only [Finset.card_range,Nat.card_Ico] using hc
  have hlow : Z.card ≤ Dlow.card+E.card+1 := by
    have hc := short_window_low_offset_count p a R E hR (by omega)
      (by interval_cases e <;> omega) hunpaid (by
        intro b hbh hgap hghi
        have hglo : R ≤ (b-p b).val := by
          by_contra hnot
          exact hgap (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
        have hgap17 : (b-p b).val < 17 := by
          by_contra hnot
          exact hgap (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,hghi⟩))
        have hf := hb.2 b
        have hr := anchor_reserve_nonneg p b
        interval_cases e
        · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩
        · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega) (by omega)
          exact ⟨w,hw,by omega⟩)
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    exact hc
  have hupper : e*m+16 < n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
      p (phase p a) (displacement p a) (is_lift p a) (global_minimum_majorized ha)
      (height p a) (by omega) (by omega)
      (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    have hcap := (candidate_price_components p a).1
    apply hunpaid
    refine ⟨w,hw,?_⟩
    interval_cases e
    · have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hnsmall : (n : ℤ) ≤ 16 := by omega
      nlinarith
    · have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      have hhsmall : (height p a : ℤ) ≤ 14 := by omega
      nlinarith
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
    have ht := short_window_terminal_threshold p a m R g e he hn hnlarge hupper hh hmin hb.2 hdepth hunpaid
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
  have hlinear : (Z.card : ℤ)-(P.card : ℤ) ≤
      (m : ℤ)-(e*m : ℕ)+3*(R : ℤ)+(E.card : ℤ)-15 := by omega
  have hquad' : ((R : ℤ)-1)*(R-2) ≤ 6*(R : ℤ)+2*E.card-30 := by
    interval_cases e
    · simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
      have hm' : (m : ℤ)=(height p a : ℤ)+1 := by omega
      nlinarith
    · simp only [Nat.one_mul] at hlinear
      have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
      nlinarith
  by_cases hRsmall : 2*R+3 ≤ 17
  · have hE' : (E.card : ℤ) ≤ R := by omega
    have hsquare := sq_nonneg (2*(R : ℤ)-11)
    nlinarith
  · have hE' : (E.card : ℤ) ≤ 3*(R : ℤ)-14 := by omega
    have hsquare := sq_nonneg (2*(R : ℤ)-15)
    nlinarith

#print axioms short_window_quadratic_upper_word
end LX.AnchoredPhases
