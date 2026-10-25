import LX.OddHeadExtraDrop
import LX.OddHeadLeastGap
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Counting the terminal window at its first higher phase requires
h+1 distinct nonzero physical backward arrows. -/
theorem rank_two_unpaid_head_drop_lower (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p a+1 ≤ (nonzeroLowerOffsetDrops p (p 0)).card := by
  classical
  let h := height p a
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  let M := minimumRawOffsets p h
  let I := Finset.Icc 1 (h+3)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  let B := P.image (fun t => p a-a+t)
  let D := nonzeroLowerOffsetDrops p (p 0)
  let V := D.image (fun i => p i-i)
  have hZ : Z.card ≤ M.card := zero_surplus_count_le_minimum_offsets p a hmin
  have hB : B.card=P.card := Finset.card_image_of_injective _ (add_right_injective (p a-a))
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
  obtain ⟨hhead,hghead,hgheadcap⟩ := rank_two_unpaid_higher_head p a hn hh hmin hR hunpaid
  have hleast := rank_two_unpaid_head_least_gap p a hn hh hmin hR hunpaid
  have hheadval : (p 0).val=n-(-p 0).val := by
    have hp0 : -p 0 ≠ 0 := Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hghead)
    conv_lhs => rw [← neg_neg (p 0)]
    rw [Fin.val_neg,ite_eq_right hp0]
  have hnonhead (b : Fin n) (hb : height p b=h) : p 0 ≠ p b-b := by
    intro he
    have hh' := equal_raw_offset_height p 0 b (by simpa using he)
    omega
  have hgap (b : Fin n) (hb : height p b=h) : h+3 < (b-p b).val :=
    odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hb (hnonhead b hb) hunpaid
  have hrawgap (b : Fin n) (hg : 0 < (b-p b).val) :
      (p b-b).val=n-(b-p b).val := by
    have he : p b-b= -(b-p b) := by ring
    rw [he,Fin.val_neg,ite_eq_right (Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hg))]
  have hinter : M ∩ W=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htM,htW⟩ := Finset.mem_inter.mp ht
    obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
    obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
    have hg' := Finset.mem_Icc.mp hg
    have hgv : (b-p b).val=g := by
      have he : b-p b=(g : Fin n) := by linear_combination -hbt+hgt
      rw [he]; exact Nat.mod_eq_of_lt (by omega)
    have hbGap := hgap b hb
    omega
  obtain ⟨z,hz⟩ := exists_unpaid_aligned_terminal_source p h hn (by omega) hunpaid
  let E : Finset (Fin n) := {p 0,p z-z}
  have hsub : M ∪ W ⊆ (B ∪ V) ∪ E := by
    intro t ht
    by_cases hex : t ∈ E
    · exact Finset.mem_union_right _ hex
    have hth : t ≠ p 0 := by intro he; exact hex (by simp [E,he])
    apply Finset.mem_union_left
    rcases Finset.mem_union.mp ht with htM | htW
    · obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
      have hbg := hgap b hb
      have ht0 : p b-b ≠ 0 := by
        intro he
        have hv : b-p b=0 := by linear_combination -he
        rw [hv,Fin.val_zero] at hbg
        omega
      have hunpaid' : ¬ ∃ w : List Letter,p*eval w=1 ∧
          4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*(1 : ℕ) := by
        rintro ⟨w,hw,hprice⟩
        exact hunpaid ⟨w,hw,by omega⟩
      obtain ⟨i,hi,hpi,hib⟩ := minimum_unpaid_positive_backward p a b 1 (by omega) (by omega)
        hh hmin hb hunpaid' ht0 (by rwa [hbt])
      have hil : (p i-i).val < (p 0).val := by
        rw [hib,hrawgap b (by omega),hheadval]
        have := (b-p b).isLt
        have := (-p 0).isLt
        omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hi,hil⟩,hpi⟩,hib.trans hbt⟩)
    · obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
      have hg' := Finset.mem_Icc.mp hg
      rcases odd_full_terminal_threshold p a z g hn hh hmin hunpaid hz hg'.1 hg'.2 with
        hhigh | hhd | hprev | halign | ⟨b,hbd,hpne,hbh,hbr⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
        rw [← hgt]; ring
      · exact False.elim (hth (hgt.symm.trans hhd))
      · have hbad := hprev.2; omega
      · exact False.elim (hex (by rw [← hgt,halign.1]; simp [E]))
      · have hbg : (b-p b).val=g := by
          have he : b-p b=(g : Fin n) := by linear_combination -hbr
          rw [he]; exact Nat.mod_eq_of_lt (by omega)
        have hle := hleast b hbh (by omega)
        have hne : (-p 0).val ≠ (b-p b).val := by
          intro he
          have he' : -p 0=b-p b := Fin.ext he
          apply hth
          rw [← hgt,← hbr]
          linear_combination he'
        have hbl : (p b-b).val < (p 0).val := by
          rw [hrawgap b (by omega),hheadval]
          have := (b-p b).isLt
          have := (-p 0).isLt
          omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbd,hbl⟩,hpne⟩,hbr.trans hgt⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (B ∪ V) E)
  have hMW := Finset.card_union_add_card_inter M W
  rw [hinter,Finset.card_empty] at hMW
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hBV := Finset.card_union_le B V
  have hE : E.card ≤ 2 := by
    have hh := Finset.card_pair_eq_one_or_two (a := p 0) (b := p z-z)
    change E.card=1 ∨ E.card=2 at hh
    omega
  have hexcess : secondExcess p a=(Z.card : ℤ)-P.card := by
    have he := second_excess_count p a hmin
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+_ at he
    rw [hn'] at he
    nlinarith only [he]
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  change h+1 ≤ D.card
  omega

theorem rank_two_unpaid_impossible (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : False := by
  have hupper := rank_two_unpaid_head_drop_upper p a hn hh hmin hR hunpaid
  have hlower := rank_two_unpaid_head_drop_lower p a hn hh hmin hR hunpaid
  omega

#print axioms rank_two_unpaid_head_drop_lower
#print axioms rank_two_unpaid_impossible
end LX.AnchoredPhases
