import LX.ConjectureTerminalWindow
import LX.EvenBinaryRankObstruction
import LX.MinimumSmallGap
import LX.SecondExcess
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

private theorem raw_value_from_gap (p : State n) (b : Fin n) (hg : 0 < (b-p b).val) :
    (p b-b).val=n-(b-p b).val := by
  have he : p b-b= -(b-p b) := by ring
  rw [he,Fin.val_neg,ite_eq_right (Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hg))]


/-- Counting below the least terminal higher phase uses its own height
`h+1`, eliminating the global rank peak from the backward-arrow budget. -/
theorem odd_unpaid_cut_second_excess (p : State n) (a : Fin n) (R : ℕ)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) (hRsmall : R ≤ height p a+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a ≤ (R : ℤ)-1 := by
  classical
  let h := height p a
  let m := h+1
  have hbase : 3*(n : ℤ)^2-8*n+9=4*(3*(h : ℤ)^2+5*h+3) := by
    have hn' : (n : ℤ)=2*(h : ℤ)+3 := by exact_mod_cast hn
    rw [hn']; ring
  have hstrict : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(1 : ℤ)) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  have hF := (rank_peak_anchor_bounds p a R hmin hR).2
  have hunpaid' : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*(1 : ℕ) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  let M := minimumRawOffsets p h
  let I := Finset.Icc (R+1) (h+3)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  let Bad := P.image (fun t => p a-a+t)
  have hZ : Z.card ≤ M.card := zero_surplus_count_le_minimum_offsets p a hmin
  have hM : M.card ≤ h+1 := unpaid_minimum_offset_count p a 1 (by omega) (by omega) hh hmin
    hunpaid'
  have hBad : Bad.card ≤ P.card := Finset.card_image_le
  have hW : W.card=h+3-R := by
    have he : W.card=I.card := by
      apply Finset.card_image_iff.mpr
      intro i hi j hj hij
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      have hc : (i : Fin n)=(j : Fin n) := neg_injective hij
      have hv := congrArg Fin.val hc
      rw [show (i : Fin n).val=i from Nat.mod_eq_of_lt (by omega),
        show (j : Fin n).val=j from Nat.mod_eq_of_lt (by omega)] at hv
      exact hv
    rw [he]
    dsimp only [I]
    rw [Nat.card_Icc]
    omega
  have hdis : Disjoint M W := by
    apply Finset.disjoint_left.mpr
    intro t htM htW
    obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
    obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
    have hg' := Finset.mem_Icc.mp hg
    have hgap : (b-p b).val=g := by
      have he : b-p b=(g : Fin n) := by linear_combination -hbt+hgt
      rw [he]
      exact Nat.mod_eq_of_lt (by omega)
    have hex := conjecture_window_terminal_low_excluded p m R 1 (by omega) (by omega)
      (by omega) hF hstrict b (by omega) (by dsimp [m]; omega)
    exact hex (by dsimp [h,m] at *; omega)
  obtain ⟨z,hz⟩ := exists_least_gap_above p m (R+1)
  have hwindow (g : ℕ) (hg : g ∈ I) :=
    conjecture_window_terminal_threshold p a z m R g 1 (by omega) (by omega)
      (by omega) (by dsimp [m]; omega) rfl hmin hF hR hz hstrict
      (Finset.mem_Icc.mp hg).1 (by have := (Finset.mem_Icc.mp hg).2; dsimp [m]; omega)
  have hexcess : secondExcess p a=(Z.card : ℤ)-P.card := by
    have he := second_excess_count p a hmin
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+_ at he
    rw [hn'] at he
    nlinarith only [he]
  by_cases hzgood : height p z=m ∧ R+1 ≤ (z-p z).val ∧ (z-p z).val ≤ h+3
  · let D := lowerOffsetDrops p (p z-z)
    let V := D.image (fun i => p i-i)
    let E : Finset (Fin n) := {p z-z,p 0}
    have hsub : M ∪ W ⊆ (Bad ∪ V) ∪ E := by
      intro t ht
      by_cases hex : t ∈ E
      · exact Finset.mem_union_right _ hex
      have hth : t ≠ p 0 := by intro he; exact hex (by simp [E,he])
      have htz : t ≠ p z-z := by intro he; exact hex (by simp [E,he])
      apply Finset.mem_union_left
      rcases Finset.mem_union.mp ht with htM | htW
      · obtain ⟨c,hc,hct⟩ := (mem_minimum_raw_offsets p h t).mp htM
        have hgap := odd_unpaid_nonhead_minimum_gap p a c hn hh hmin hc
          (by rw [hct]; exact Ne.symm hth) hunpaid
        have ht0 : p c-c ≠ 0 := by
          intro he
          have hv : c-p c=0 := by linear_combination -he
          rw [hv,Fin.val_zero] at hgap
          omega
        obtain ⟨i,hi,_,hic⟩ := minimum_unpaid_positive_backward p a c 1 (by omega) (by omega)
          hh hmin hc hunpaid' ht0 (by rwa [hct])
        have hil : (p i-i).val < (p z-z).val := by
          rw [hic,raw_value_from_gap p c (by omega),raw_value_from_gap p z (by omega)]
          have hgcn := (c-p c).isLt
          have hgzn := (z-p z).isLt
          omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨hi,hil⟩,hic.trans hct⟩)
      · obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
        rcases hwindow g hg with hhigh | hhead | hspecial | ⟨c,hcd,hch,hcr⟩
        · apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
          rw [← hgt]
          ring
        · exact False.elim (hth (hgt.symm.trans hhead.1))
        · exact False.elim (htz (hgt.symm.trans hspecial))
        · have hg' := Finset.mem_Icc.mp hg
          have hgap : (c-p c).val=g := by
            have he : c-p c=(g : Fin n) := by linear_combination -hcr
            rw [he]
            exact Nat.mod_eq_of_lt (by omega)
          have hzg := hz c hch (by omega)
          have hgneq : (z-p z).val ≠ (c-p c).val := by
            intro he
            have he' : z-p z=c-p c := Fin.ext he
            apply htz
            rw [← hgt,← hcr]
            linear_combination he'
          have hcl : (p c-c).val < (p z-z).val := by
            rw [raw_value_from_gap p c (by omega),raw_value_from_gap p z (by omega)]
            have := (c-p c).isLt
            have := (z-p z).isLt
            omega
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨c,Finset.mem_filter.mpr ⟨hcd,hcl⟩,hcr.trans hgt⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ V) E)
    rw [Finset.card_union_of_disjoint hdis] at hc
    have hv : V.card ≤ D.card := Finset.card_image_le
    have hBV := Finset.card_union_le Bad V
    have hd := lower_offset_drop_bound p z
    change D.card+(if p 0=p z-z then 0 else 1) ≤ height p z at hd
    have hE : E.card ≤ 1+(if p 0=p z-z then 0 else 1) := by
      by_cases hh : p 0=p z-z
      · simp [E,hh]
      · rw [ite_eq_right hh]
        have hp' := Finset.card_pair_eq_one_or_two (a := p z-z) (b := p 0)
        change ({p z-z,p 0} : Finset (Fin n)).card ≤ 1+1
        omega
    rw [hexcess]
    dsimp only [m] at hzgood
    omega
  · have hsub : W ⊆ Bad := by
      intro t ht
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp ht
      have hg' := Finset.mem_Icc.mp hg
      let u : Fin n := -(g : Fin n)-(p a-a)
      have hnonneg := rank_surplus_nonnegative p a hmin u.val (Nat.le_of_lt u.isLt)
      have hhigh : 2 ≤ rankSurplus p a u.val := by
        by_contra hnot
        have hnonzero : rankSurplus p a u.val ≠ 0 := by
          intro hu
          obtain ⟨c,hc,hheight⟩ := zero_surplus_anchor p a hmin u hu
          have hcr : p c-c= -(g : Fin n) := by
            dsimp only [u] at hc
            unfold cyclicOffset at hc
            linear_combination hc
          have hgap : (c-p c).val=g := by
            have he : c-p c=(g : Fin n) := by linear_combination -hcr
            rw [he]
            exact Nat.mod_eq_of_lt (by omega)
          exact conjecture_window_terminal_low_excluded p m R 1 (by omega) (by omega)
            (by omega) hF hstrict c (by omega) (by dsimp [m]; omega) (by dsimp [m,h]; omega)
        have hone : rankSurplus p a u.val=1 := by omega
        rcases rank_one_occupied_or_next_minimum p a u hmin hone with
          ⟨c,hc,hheight⟩ | ⟨c,hc,hheight⟩
        · have hcr : p c-c= -(g : Fin n) := by
            dsimp only [u] at hc
            unfold cyclicOffset at hc
            linear_combination hc
          have hgap : (c-p c).val=g := by
            have he : c-p c=(g : Fin n) := by linear_combination -hcr
            rw [he]
            exact Nat.mod_eq_of_lt (by omega)
          have hzg := hz c hheight (by omega)
          exact hzgood ⟨hzg.1,hzg.2.1,by omega⟩
        · have hcr : p c-c= -((g-1 : ℕ) : Fin n) := by
            dsimp only [u] at hc
            unfold cyclicOffset at hc
            rw [Nat.cast_sub (by omega : 1 ≤ g),Nat.cast_one]
            linear_combination hc
          have hgap : (c-p c).val=g-1 := by
            have he : c-p c=((g-1 : ℕ) : Fin n) := by linear_combination -hcr
            rw [he]
            exact Nat.mod_eq_of_lt (by omega)
          exact conjecture_window_terminal_low_excluded p m R 1 (by omega) (by omega)
            (by omega) hF hstrict c (by omega) (by dsimp [m]; omega) (by dsimp [m,h]; omega)
      apply Finset.mem_image.mpr
      refine ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
      rw [← hgt]
      dsimp only [u]
      ring
    have hc := Finset.card_le_card hsub
    rw [hexcess]
    omega

#print axioms odd_unpaid_cut_second_excess
end LX.AnchoredPhases
