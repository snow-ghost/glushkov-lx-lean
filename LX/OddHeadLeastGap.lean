import LX.OddAlignedHeadFiber

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The head is the first positive-gap phase of height h+1. The only
possible smaller gap would be one before a gap-two head; the literal
near-top prefix forces an additional occurrence of the head offset and
raises that intervening phase's height. -/
theorem rank_two_unpaid_head_least_gap (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∀ c : Fin n,height p c=height p a+1 → 0 < (c-p c).val →
      (-p 0).val ≤ (c-p c).val := by
  classical
  intro c hch hcg
  by_contra hnot
  obtain ⟨b,hb⟩ := rank_two_unpaid_aligned_exists p a hn hh hmin hR hunpaid
  let q := permutation p b
  let k := q 0
  let g := (b-p b).val
  let F := fixedPositions q
  let A := Finset.Ioo (0 : Fin n) k
  let B := Finset.univ.filter fun i : Fin n => (cyclicOffset p b i).val < k.val
  have hkoff : cyclicOffset p b 0=k := by rw [cyclic_offset_normalized,sub_zero]
  obtain ⟨hbafter,hdcap⟩ := rank_two_unpaid_aligned_source_after_head_offset p a b hn hh hmin hR hb hunpaid
  obtain ⟨hhead,hdpos,_⟩ := rank_two_unpaid_higher_head p a hn hh hmin hR hunpaid
  obtain ⟨hdg,hkg⟩ := rank_two_unpaid_head_before_aligned_finish p a b hn hh hmin hR hb hunpaid
  have hF := rank_two_unpaid_aligned_head_fiber p a b hn hh hmin hR hb hunpaid
  obtain ⟨hFpos,hFcap,_,_,hkpos,_⟩ := rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  rw [hkoff] at hbafter hkg hF hkpos
  change F.card=k.val at hF
  change 1 ≤ F.card at hFpos
  change F.card ≤ 2 at hFcap
  have hd2 : (-p 0).val=2 := by omega
  have hgc1 : (c-p c).val=1 := by omega
  have hgk : g=k.val+2 := by dsimp only [g]; omega
  have hfinish := hb.2.2.2.1
  have hbupper : b.val ≤ g := by dsimp only [g]; omega
  have hq0 : q 0 ≠ 0 := Fin.ne_of_val_ne (by change k.val ≠ 0; omega)
  have hheight := hb.1
  have hpre := odd_unpaid_aligned_prefix p (height p a) b hn (by omega) hb hunpaid
  have hf := near_top_prefix_forward p b (g+1) (by omega) hq0
    (fun i hi => hpre i (by omega))
  have hAF : A ⊆ F := by
    intro i hi
    have hi' := Finset.mem_Ioo.mp hi
    exact (mem_fixedPositions _ _).mpr ((hf 0 (by simp [g])).2 i hi'.1 hi'.2)
  have hAcard : A.card=k.val-1 := by dsimp only [A]; rw [Fin.card_Ioo,Fin.val_zero]; omega
  have hbA : b ∉ A := by intro hi; have := (Finset.mem_Ioo.mp hi).2; omega
  have hbF : b ∈ F := (mem_fixedPositions _ _).mpr (permutation_anchor p b)
  have hFeq : F=insert b A := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hbF hAF)
    rw [Finset.card_insert_of_notMem hbA]
    omega
  have hmove (i : Fin n) (hik : k.val ≤ i.val) (hib : i.val ≠ b.val) : q i ≠ i := by
    intro he
    have hi : i ∈ insert b A := hFeq ▸ (mem_fixedPositions _ _).mpr he
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact hib (congrArg Fin.val hi)
    · have := (Finset.mem_Ioo.mp hi).2; omega
  let jv : ℕ := if b.val=k.val+1 then k.val+2 else k.val
  have hjlo : k.val ≤ jv := by dsimp only [jv]; split_ifs <;> omega
  have hjhi : jv ≤ g := by dsimp only [jv]; split_ifs <;> omega
  have hjb : jv ≠ b.val := by dsimp only [jv]; split_ifs <;> omega
  have hj1b : jv+1 ≠ b.val := by dsimp only [jv]; split_ifs <;> omega
  let j : Fin n := ⟨jv,by omega⟩
  let j1 : Fin n := ⟨jv+1,by omega⟩
  have hjmove : q j ≠ j := hmove j hjlo hjb
  have hj1move : q j1 ≠ j1 := hmove j1 (by change k.val ≤ jv+1; omega) hj1b
  have hfj := hf j (by change jv < g+1; omega)
  have hjstep : (q j).val=jv+1 := by
    have hle : jv ≤ (q j).val := hfj.1
    have hne : (q j).val ≠ jv := fun he => hjmove (Fin.ext he)
    by_contra hnot
    exact hj1move (hfj.2 j1 (by change jv < jv+1; omega) (by change jv+1 < (q j).val; omega))
  have hunit : (cyclicOffset p b j).val=1 := by
    rw [cyclic_offset_normalized,Fin.coe_sub_iff_le.mpr hfj.1]
    change (q j).val-jv=1
    omega
  have hFB : F ⊆ B := by
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  have hBcard : B.card=k.val := by
    have ht := reanchor_height p b 0
    rw [hkoff,hhead,hheight] at ht
    change _= _-(k.val : ℤ)+B.card at ht
    omega
  have hBF : B=F := (Finset.eq_of_subset_of_card_le hFB (by omega)).symm
  have hk1 : k.val=1 := by
    by_contra hnot
    have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hunit]; omega⟩
    have hjF : j ∈ F := hBF ▸ hjB
    exact hjmove ((mem_fixedPositions _ _).mp hjF)
  have hoffc : (cyclicOffset p b c).val=2 := by
    have he : cyclicOffset p b c=(b-p b)-(c-p c) := by unfold cyclicOffset; ring
    rw [he,Fin.coe_sub_iff_le.mpr (show c-p c ≤ b-p b by change (c-p c).val ≤ g; omega)]
    change g-(c-p c).val=2
    omega
  let B2 := Finset.univ.filter fun i : Fin n => (cyclicOffset p b i).val < 2
  have hB2 : B2.card=2 := by
    have ht := reanchor_height p b c
    rw [hch,hheight,hoffc] at ht
    change _= _-(2 : ℤ)+(B2.card : ℤ) at ht
    omega
  have hFB2 : F ⊆ B2 := by
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  have hzeroB : (0 : Fin n) ∈ B2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hkoff,hk1]; omega⟩
  have hjB : j ∈ B2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hunit]; omega⟩
  have hzF : (0 : Fin n) ∉ F := fun hi => hq0 ((mem_fixedPositions _ _).mp hi)
  have hjF : j ∉ F := fun hi => hjmove ((mem_fixedPositions _ _).mp hi)
  have hzj : (0 : Fin n) ≠ j := by
    intro he; have hv := congrArg Fin.val he; change 0=jv at hv; omega
  have hc := Finset.card_le_card (Finset.insert_subset hzeroB (Finset.insert_subset hjB hFB2))
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert] using not_or_intro hzj hzF),
    Finset.card_insert_of_notMem hjF,hB2] at hc
  omega

#print axioms rank_two_unpaid_head_least_gap
end LX.AnchoredPhases
