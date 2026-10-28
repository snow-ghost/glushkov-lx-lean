import LX.FiberDepthGeometry
import LX.OddFullTerminalWindow
import LX.SecondExcess
import Mathlib

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

private theorem raw_gap_value (p : State n) (b : Fin n) (hg : 0 < (b-p b).val) :
    (p b-b).val=n-(b-p b).val := by
  have he : p b-b= -(b-p b) := by ring
  rw [he,Fin.val_neg,ite_eq_right (Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hg))]

theorem odd_unpaid_head_terminal_zero_high (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hhead : height p 0=height p a)
    (hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    2 ≤ rankSurplus p a (-(p a-a)).val := by
  have hf : (-p 0).val+2 ≤ (fixedPositions (permutation p 0)).card := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p 0 (by omega) (by omega)
      (by simp only [zero_sub]; omega)
    have hr := anchor_reserve_nonneg p 0
    simp only [zero_sub] at hprice
    exact hunpaid ⟨w,hw,by omega⟩
  have hbelow : (fixedPositions (permutation p 0)).card ≤ belowCount p 0 (-p 0).val := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p 0 i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; exact hg1⟩
  have hzero : 2 ≤ rankSurplus p 0 (-p 0).val := by unfold rankSurplus; omega
  have ht := rank_profile_reanchor p a 0 (-p 0)
  have he : cyclicOffset p a 0+(-p 0)= -(p a-a) := by unfold cyclicOffset; ring
  rw [he,hhead] at ht
  omega

def HeadPredecessorTerminal (p : State n) (h : ℕ) : Prop :=
  height p 0=h ∧ 0 < (1-p 0).val ∧ (1-p 0).val ≤ h+3

def SmallerHigherAlignedTerminal (p : State n) (h : ℕ) : Prop :=
  ∃ b c : Fin n,HigherAlignedTerminal p h b ∧ height p c=h+1 ∧
    0 < (c-p c).val ∧ (c-p c).val < (b-p b).val

def RelevantTerminalHead (p : State n) (h : ℕ) : Prop :=
  height p 0=h ∨ (height p 0=h+1 ∧ 0 < (-p 0).val ∧ (-p 0).val ≤ h+3)

/-- Each unit left by the complete window count requires an actual
exception: the minimum-head predecessor and an aligned higher phase. -/
theorem odd_unpaid_second_excess_head_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+2 ≤ ((if RelevantTerminalHead p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if HeadPredecessorTerminal p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if SmallerHigherAlignedTerminal p (height p a) then 1 else 0 : ℕ) : ℤ) := by
  classical
  let h := height p a
  let K := HeadPredecessorTerminal p h
  let J := ∃ b,HigherAlignedTerminal p h b
  let S := SmallerHigherAlignedTerminal p h
  let T := RelevantTerminalHead p h
  let ET : Finset (Fin n) := if T then {p 0} else ∅
  have hET : ET.card=(if T then 1 else 0) := by dsimp only [ET]; split_ifs <;> simp
  let EH : Finset (Fin n) := if K then {p 0-1} else ∅
  have hEH : EH.card=(if K then 1 else 0) := by dsimp only [EH]; split_ifs <;> simp
  change secondExcess p a+2 ≤ ((if T then 1 else 0 : ℕ) : ℤ)+
    ((if K then 1 else 0 : ℕ) : ℤ)+((if S then 1 else 0 : ℕ) : ℤ)
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  let M := minimumRawOffsets p h
  let I := Finset.Icc 1 (h+3)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  let B := P.image (fun t => p a-a+t)
  let Bad := B.erase 0
  have hZ : Z.card ≤ M.card := zero_surplus_count_le_minimum_offsets p a hmin
  have hunpaid' : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*(1 : ℕ) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  have hM : M.card ≤ h+1 := unpaid_minimum_offset_count p a 1 (by omega) (by omega) hh hmin hunpaid'
  have hB : B.card=P.card := Finset.card_image_of_injective _ (add_right_injective (p a-a))
  have hBad : Bad.card ≤ P.card := (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq hB
  have hWzero : (0 : Fin n) ∉ W := by
    intro hz
    obtain ⟨g,hg,hg0⟩ := Finset.mem_image.mp hz
    have hg' := Finset.mem_Icc.mp hg
    have he : (g : Fin n)=0 := neg_eq_zero.mp hg0
    have hv := congrArg Fin.val he
    rw [show (g : Fin n).val=g from Nat.mod_eq_of_lt (by omega),Fin.val_zero] at hv
    omega
  have hW : W.card=h+3 := by
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
  have hheadBad (ht : p 0 ∈ M ∪ W) (hT : ¬ T) : p 0 ∈ Bad := by
    rcases Finset.mem_union.mp ht with htM | htW
    · obtain ⟨b,hb,hbr⟩ := (mem_minimum_raw_offsets p h (p 0)).mp htM
      have he : height p 0=h :=
        (equal_raw_offset_height p 0 b (by simpa using hbr.symm)).trans hb
      exact False.elim (hT (Or.inl he))
    · obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
      have hg' := Finset.mem_Icc.mp hg
      have hgap : (-p 0).val=g := by
        rw [← hgt,neg_neg]
        exact Nat.mod_eq_of_lt (by omega)
      have hhlo : h+2 ≤ height p 0 := by
        have hmin0 := hmin 0
        by_contra hnot
        by_cases he : height p 0=h
        · exact hT (Or.inl he)
        · exact hT (Or.inr ⟨by omega,by omega,by omega⟩)
      have hr : 2 ≤ rankSurplus p a (p 0-(p a-a)).val := by
        have ht := reanchor_height p a 0
        simp only [cyclicOffset,sub_zero] at ht
        unfold rankSurplus
        omega
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_image.mpr ⟨p 0-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,by ring⟩⟩
      intro he
      have hw : p 0 ∈ W := Finset.mem_image.mpr ⟨g,hg,hgt⟩
      exact hWzero (he ▸ hw)
  have hinterHead : M ∩ W ⊆ {p 0} := by
      intro t ht
      obtain ⟨htM,htW⟩ := Finset.mem_inter.mp ht
      obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
      have hg' := Finset.mem_Icc.mp hg
      have hgap : (b-p b).val=g := by
        have he : b-p b=(g : Fin n) := by linear_combination -hbt+hgt
        rw [he]
        exact Nat.mod_eq_of_lt (by omega)
      have hhead : p 0=p b-b := by
        by_contra hnot
        have hc := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hb hnot hunpaid
        omega
      exact Finset.mem_singleton.mpr (hbt.symm.trans hhead.symm)
  have hinter : (M ∩ W).card ≤ 1 := by
    simpa only [Finset.card_singleton] using Finset.card_le_card hinterHead
  have hBadinter : Bad.card+(M ∩ W).card ≤ P.card := by
    by_cases hex : (M ∩ W).Nonempty
    · obtain ⟨t,ht⟩ := hex
      have ht0 : t=p 0 := Finset.mem_singleton.mp (hinterHead ht)
      have hheadM : p 0 ∈ M := ht0 ▸ (Finset.mem_inter.mp ht).1
      have hheadW : p 0 ∈ W := ht0 ▸ (Finset.mem_inter.mp ht).2
      obtain ⟨b,hb,hraw⟩ := (mem_minimum_raw_offsets _ _ _).mp hheadM
      have hheight : height p 0=height p a :=
        (equal_raw_offset_height p 0 b (by simpa using hraw.symm)).trans hb
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp hheadW
      have hg' := Finset.mem_Icc.mp hg
      have hgap : (-p 0).val=g := by
        rw [← hgt,neg_neg]
        exact Nat.mod_eq_of_lt (by omega)
      have hr := odd_unpaid_head_terminal_zero_high p a hn hh hheight (by omega) (by omega) hunpaid
      have hzB : (0 : Fin n) ∈ B := by
        apply Finset.mem_image.mpr
        refine ⟨-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,?_⟩
        ring
      have hcard : Bad.card=P.card-1 := by dsimp only [Bad]; rw [Finset.card_erase_of_mem hzB,hB]
      have hpos : 0 < P.card := by rw [← hB]; exact Finset.card_pos.mpr ⟨0,hzB⟩
      omega
    · have hz : (M ∩ W).card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hex)
      omega
  obtain ⟨z,hz⟩ := exists_unpaid_aligned_terminal_source p h hn (by omega) hunpaid
  let EA : Finset (Fin n) := if J then {p z-z} else ∅
  have hEA : EA.card=(if J then 1 else 0) := by dsimp only [EA]; split_ifs <;> simp
  have hpred (g : ℕ) (hg : g ∈ I) (he : -(g : Fin n)=p 0-1) (hheight : height p 0=height p a) : K := by
    have hg' := Finset.mem_Icc.mp hg
    have hval : (1-p 0).val=g := by
      have he' : (1-p 0 : Fin n)=(g : Fin n) := by linear_combination he
      rw [he']
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨hheight,by omega,by omega⟩
  obtain ⟨c,hc⟩ := exists_least_gap_above p (h+1) 1
  have hwindow (g : ℕ) (hg : g ∈ I) := odd_full_terminal_threshold p a z g hn hh hmin hunpaid hz
    (Finset.mem_Icc.mp hg).1 (Finset.mem_Icc.mp hg).2
  have hexcess : secondExcess p a=(Z.card : ℤ)-P.card := by
    have he := second_excess_count p a hmin
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+_ at he
    rw [hn'] at he
    nlinarith only [he]
  by_cases hcgood : height p c=h+1 ∧ 1 ≤ (c-p c).val ∧ (c-p c).val ≤ h+3
  · let D := lowerOffsetDrops p (p c-c)
    let V := D.image (fun i => p i-i)
    let E : Finset (Fin n) := ((ET ∪ {p c-c}) ∪ EH) ∪ EA
    have hsub : M ∪ W ⊆ (Bad ∪ V) ∪ E := by
      intro t ht
      by_cases hex : t ∈ E
      · exact Finset.mem_union_right _ hex
      by_cases htBad : t ∈ Bad
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ htBad)
      have hth : t ≠ p 0 := by
        intro he
        by_cases hT : T
        · exact hex (by simp [E,ET,hT,he])
        · exact htBad (he ▸ hheadBad (he ▸ ht) hT)
      have htc : t ≠ p c-c := by intro he; exact hex (by simp [E,he])
      apply Finset.mem_union_left
      rcases Finset.mem_union.mp ht with htM | htW
      · obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
        have hgap := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hb
          (by rw [hbt]; exact Ne.symm hth) hunpaid
        have ht0 : p b-b ≠ 0 := by
          intro he
          have hv : b-p b=0 := by linear_combination -he
          rw [hv,Fin.val_zero] at hgap
          omega
        obtain ⟨i,hi,_,hib⟩ := minimum_unpaid_positive_backward p a b 1 (by omega) (by omega)
          hh hmin hb hunpaid' ht0 (by rwa [hbt])
        have hil : (p i-i).val < (p c-c).val := by
          rw [hib,raw_gap_value p b (by omega),raw_gap_value p c (by omega)]
          have := (b-p b).isLt
          have := (c-p c).isLt
          omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_filter.mpr ⟨hi,hil⟩,hib.trans hbt⟩)
      · have ht0 : t ≠ 0 := by intro he; exact hWzero (he ▸ htW)
        obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
        rcases hwindow g hg with hhigh | hhead | hprev | halign | ⟨b,hbd,_,hbh,hbr⟩
        · apply Finset.mem_union_left
          apply Finset.mem_erase.mpr
          refine ⟨ht0,?_⟩
          apply Finset.mem_image.mpr
          refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
          rw [← hgt]; ring
        · exact False.elim (hth (hgt.symm.trans hhead))
        · have hK := hpred g hg hprev.1 hprev.2
          exact False.elim (hex (by rw [← hgt,hprev.1]; simp [E,EH,hK]))
        · have hJ : J := halign.2
          exact False.elim (hex (by rw [← hgt,halign.1]; simp [E,EA,hJ]))
        · have hg' := Finset.mem_Icc.mp hg
          have hgap : (b-p b).val=g := by
            have he : b-p b=(g : Fin n) := by linear_combination -hbr
            rw [he]; exact Nat.mod_eq_of_lt (by omega)
          have hcg := hc b hbh (by omega)
          have hgneq : (c-p c).val ≠ (b-p b).val := by
            intro he
            have he' : c-p c=b-p b := Fin.ext he
            apply htc
            rw [← hgt,← hbr]
            linear_combination he'
          have hbl : (p b-b).val < (p c-c).val := by
            rw [raw_gap_value p b (by omega),raw_gap_value p c (by omega)]
            have := (b-p b).isLt
            have := (c-p c).isLt
            omega
          exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨b,Finset.mem_filter.mpr ⟨hbd,hbl⟩,hbr.trans hgt⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ V) E)
    have hMW := Finset.card_union_add_card_inter M W
    have hv : V.card ≤ D.card := Finset.card_image_le
    have hBV := Finset.card_union_le Bad V
    have hd := lower_offset_drop_bound p c
    change D.card+(if p 0=p c-c then 0 else 1) ≤ height p c at hd
    have hct (he : p 0=p c-c) : T := by
      have heh : height p 0=height p c := equal_raw_offset_height p 0 c (by simpa using he)
      have heg : -p 0=c-p c := by linear_combination -he
      exact Or.inr ⟨heh.trans hcgood.1,by rw [heg]; omega,by rw [heg]; exact hcgood.2.2⟩
    have hbase : (ET ∪ {p c-c}).card ≤ (if T then 1 else 0)+(if p 0=p c-c then 0 else 1) := by
      by_cases hp0 : p 0=p c-c
      · simp [ET,hct hp0,hp0]
      · rw [ite_eq_right hp0]
        have hc := Finset.card_union_le ET {p c-c}
        rw [Finset.card_singleton,hET] at hc
        exact hc
    have hEold : E.card ≤ (if T then 1 else 0)+(if p 0=p c-c then 0 else 1)+EH.card+EA.card := by
      have h1 := Finset.card_union_le ((ET ∪ {p c-c}) ∪ EH) EA
      have h2 := Finset.card_union_le (ET ∪ {p c-c}) EH
      change E.card ≤ _ at h1
      omega
    have hE : E.card ≤ (if T then 1 else 0)+(if p 0=p c-c then 0 else 1)+EH.card+(if S then 1 else 0) := by
      by_cases hs : S
      · rw [ite_eq_left hs]
        split_ifs at hEA <;> omega
      · have hsubEA : EA ⊆ {p c-c} := by
          intro t ht
          by_cases hj : J
          · obtain ⟨b,hb⟩ := hj
            have hcb := hc b hb.1 (by have := hb.2.2.2.2.1; omega)
            have hge : (c-p c).val=(b-p b).val := by
              by_contra hne
              exact hs ⟨b,c,hb,hcgood.1,by omega,by omega⟩
            have he : p z-z=p c-c := by
              have hr := hz b hb
              have hg := Fin.ext hge
              linear_combination -hr+hg
            have ht' : t=p z-z := by simpa only [EA,ite_eq_left (show J from ⟨b,hb⟩),Finset.mem_singleton] using ht
            exact Finset.mem_singleton.mpr (ht'.trans he)
          · simp only [EA,ite_eq_right hj,Finset.notMem_empty] at ht
        have heSub : E ⊆ (ET ∪ {p c-c}) ∪ EH := by
          intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact ht
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hsubEA ht))
        have heCard := (Finset.card_le_card heSub).trans (Finset.card_union_le _ _)
        rw [ite_eq_right hs]
        omega
    rw [hexcess]
    omega
  · let E : Finset (Fin n) := (ET ∪ EH) ∪ EA
    have hJfalse : ¬ J := by
      rintro ⟨b,hb⟩
      have hcb := hc b hb.1 (by have := hb.2.2.2.2.1; omega)
      have hbg := hb.2.2.2.2.2
      exact hcgood ⟨hcb.1,hcb.2.1,by omega⟩
    rw [ite_eq_right hJfalse] at hEA
    have hsub : W ⊆ Bad ∪ E := by
      intro t ht
      have ht0 : t ≠ 0 := by intro he; exact hWzero (he ▸ ht)
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp ht
      rcases hwindow g hg with hhigh | hhead | hprev | halign | ⟨b,_,_,hbh,hbr⟩
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        refine ⟨ht0,?_⟩
        apply Finset.mem_image.mpr
        refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
        rw [← hgt]; ring
      · by_cases hT : T
        · exact Finset.mem_union_right _ (by rw [← hgt,hhead]; simp [E,ET,hT])
        · apply Finset.mem_union_left
          have he : t=p 0 := hgt.symm.trans hhead
          exact he ▸ hheadBad (Finset.mem_union_right _ (he ▸ ht)) hT
      · have hK := hpred g hg hprev.1 hprev.2
        exact Finset.mem_union_right _ (by rw [← hgt,hprev.1]; simp [E,EH,hK])
      · have hJ : J := halign.2
        exact Finset.mem_union_right _ (by rw [← hgt,halign.1]; simp [E,EA,hJ])
      · have hg' := Finset.mem_Icc.mp hg
        have hgap : (b-p b).val=g := by
          have he : b-p b=(g : Fin n) := by linear_combination -hbr
          rw [he]; exact Nat.mod_eq_of_lt (by omega)
        have hcg := hc b hbh (by omega)
        exact False.elim (hcgood ⟨hcg.1,hcg.2.1,by omega⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le Bad E)
    have hE : E.card ≤ (if T then 1 else 0)+EH.card+EA.card := by
      have h1 := Finset.card_union_le (ET ∪ EH) EA
      have h2 := Finset.card_union_le ET EH
      change E.card ≤ _ at h1
      omega
    rw [hexcess]
    omega

theorem odd_unpaid_second_excess_smaller_phase_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤ ((if HeadPredecessorTerminal p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if SmallerHigherAlignedTerminal p (height p a) then 1 else 0 : ℕ) : ℤ) := by
  have hb := odd_unpaid_second_excess_head_bound p a hn hh hmin hunpaid
  split_ifs at hb ⊢ <;> omega

theorem odd_unpaid_second_excess_exception_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤ ((if HeadPredecessorTerminal p (height p a) then 1 else 0 : ℕ) : ℤ)+
      ((if ∃ b,HigherAlignedTerminal p (height p a) b then 1 else 0 : ℕ) : ℤ) := by
  have hb := odd_unpaid_second_excess_smaller_phase_bound p a hn hh hmin hunpaid
  by_cases hs : SmallerHigherAlignedTerminal p (height p a)
  · rw [ite_eq_left hs] at hb
    obtain ⟨b,c,hb',_⟩ := hs
    have hj : ∃ b,HigherAlignedTerminal p (height p a) b := ⟨b,hb'⟩
    simpa only [ite_eq_left hj] using hb
  · rw [ite_eq_right hs] at hb
    split_ifs at hb ⊢ <;> omega

theorem odd_unpaid_second_excess_le_one (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : secondExcess p a ≤ 1 := by
  have hb := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  split_ifs at hb <;> omega

#print axioms odd_unpaid_second_excess_exception_bound
#print axioms odd_unpaid_second_excess_head_bound
#print axioms odd_unpaid_second_excess_smaller_phase_bound
#print axioms odd_unpaid_second_excess_le_one
end LX.AnchoredPhases
