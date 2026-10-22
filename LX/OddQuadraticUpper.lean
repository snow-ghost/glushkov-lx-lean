import LX.OddTerminalWindow

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The requested word bound for every odd size. The two height classes are
counted together; the second rank excess pays all higher thresholds. -/
theorem odd_quadratic_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8192 := by
  classical
  by_contra hunpaid
  have hunpaid32 : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by linarith⟩
  have hnlarge : 4096 < n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ) ≤ 4096 := by omega
    linarith
  obtain ⟨a,ha,hh⟩ := odd_unpaid_lower_global_minimum hn4 p m hn hunpaid32
  have hmin (b : Fin n) : height p a ≤ height p b := by
    by_contra hnot
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
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by omega
    nlinarith
  have hb := rank_peak_anchor_bounds p a R hmin hR
  let K := 3*R+3
  have hdepth (b : Fin n) : depthCount (displacement p b) (height p b-1) ≤ 3*R+3 := by
    have hc := bounded_height_next_depth p (height p a) R (R+1) hb.1 hb.2 b
      (by have := hmin b; omega)
    omega
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  have hquad : ((R : ℤ)-1)*(R-2) ≤ 2*(Z.card : ℤ)-2*(P.card : ℤ) :=
    odd_minimum_count_minus_high_count p a r R hmin (by omega) hRpos hpeak
  let Dlow := (descendingPositions p).filter fun b => height p b=height p a
  let Dhigh := (descendingPositions p).filter fun b => height p b=m
  have hlow : Z.card ≤ Dlow.card+K+1 := by
    have hc := unpaid_lower_height_offset_low_arrow_count p (height p a) R (R+1)
      hb.1 hb.2 (by omega) (Or.inr (by omega)) hunpaid32
    rw [← zero_surplus_count_eq_minimum_offsets p a hmin] at hc
    change Z.card ≤ Dlow.card+R+2*(R+1)+2 at hc
    dsimp only [K]
    omega
  let I := Finset.Icc (K+2) (m+100)
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
  have hWlower : (m : ℤ)+99-(K : ℤ) ≤ W.card := by
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
    have ht := odd_terminal_threshold p a m R g hn hnlarge hh hmin hb.2 hdepth hunpaid
      (by dsimp [K] at hg'; omega) hg'.2
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
  have hdesc := bounded_height_descending_count p (height p a) R (R+1) hb.1 hb.2
  have hlinear : (Z.card : ℤ)-(P.card : ℤ) ≤ 8*(R : ℤ)-92 := by
    dsimp only [K] at *
    omega
  have hsquare := sq_nonneg (2*(R : ℤ)-19)
  nlinarith

#print axioms odd_quadratic_upper_word
end LX.AnchoredPhases
