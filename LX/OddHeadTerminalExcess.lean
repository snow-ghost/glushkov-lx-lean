import LX.OddHeadPredecessorCut
import LX.OddWideCutCount
import LX.OddZeroHeadCut
import Mathlib

namespace LX.AnchoredPhases
open Classical
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A terminal minimum head forces zero second excess. Its unoccupied
predecessor cut removes the extra exceptional occupied phase. -/
theorem odd_unpaid_small_head_aligned_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤
      ((if ∃ b,HigherAlignedTerminal p (height p a) b then 1 else 0 : ℕ) : ℤ) := by
  classical
  let h := height p a
  let cut := p 0-1
  have hcuts : height p a ≤ (p 0-1).val ∧ p 0 ≠ p 0-1 ∧
      thresholdHeight p (p 0-1)=height p a+1 ∧
      (∀ b,p b-b ≠ p 0-1) ∧
      (∀ b,height p b=height p a+1 → (p b-b).val < (p 0-1).val) := by
    by_cases hp0 : p 0=0
    · exact odd_unpaid_zero_head_predecessor_cut p a hn hh hmin hhead hp0 hunpaid
    · exact odd_unpaid_head_predecessor_cut p a hn hh hmin hR hhead
        (Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hp0)) hg2 hunpaid
  obtain ⟨hcutlow,hcuthead,hcutheight,_,hcutupper⟩ := hcuts
  let Z := Finset.univ.filter fun t : Fin n => rankSurplus p a t.val=0
  let P := Finset.univ.filter fun t : Fin n => 2 ≤ rankSurplus p a t.val
  let M := minimumRawOffsets p h
  let I := Finset.Icc 1 (h+3)
  let W := I.image (fun g : ℕ => -(g : Fin n))
  let B := P.image (fun t => p a-a+t)
  let Bad := B.erase 0
  have hZ : Z.card ≤ M.card := zero_surplus_count_le_minimum_offsets p a hmin
  have hB : B.card=P.card := Finset.card_image_of_injective _ (add_right_injective (p a-a))
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
  have hinterHead : M ∩ W ⊆ {p 0} := by
      intro t ht
      obtain ⟨htM,htW⟩ := Finset.mem_inter.mp ht
      obtain ⟨b,hb,hbt⟩ := (mem_minimum_raw_offsets p h t).mp htM
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
      have hg' := Finset.mem_Icc.mp hg
      have hgap : (b-p b).val=g := by
        have he : b-p b=(g : Fin n) := by linear_combination -hbt+hgt
        rw [he]; exact Nat.mod_eq_of_lt (by omega)
      have hheadb : p 0=p b-b := by
        by_contra hnot
        have hc := odd_unpaid_nonhead_minimum_gap p a b hn hh hmin hb hnot hunpaid
        omega
      exact Finset.mem_singleton.mpr (hbt.symm.trans hheadb.symm)
  have hinter : (M ∩ W).card ≤ 1 := by
    simpa only [Finset.card_singleton] using Finset.card_le_card hinterHead
  have hBadinter : Bad.card+(M ∩ W).card ≤ P.card := by
    by_cases hp0 : p 0=0
    · have hiempty : M ∩ W=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        have ht0 : t=0 := (Finset.mem_singleton.mp (hinterHead ht)).trans hp0
        exact hWzero (ht0 ▸ (Finset.mem_inter.mp ht).2)
      have hBad : Bad.card ≤ P.card := (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq hB
      rw [hiempty,Finset.card_empty]
      omega
    · have hzeroHigh := odd_unpaid_head_terminal_zero_high p a hn hh hhead
        (Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hp0)) hg2 hunpaid
      have hzB : (0 : Fin n) ∈ B := by
        apply Finset.mem_image.mpr
        refine ⟨-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzeroHigh⟩,?_⟩
        ring
      have hc : Bad.card=P.card-1 := by dsimp only [Bad]; rw [Finset.card_erase_of_mem hzB,hB]
      have hp : 0 < P.card := by rw [← hB]; exact Finset.card_pos.mpr ⟨0,hzB⟩
      omega
  obtain ⟨z,hz⟩ := exists_unpaid_aligned_terminal_source p h hn (by omega) hunpaid
  let D := lowerOffsetDrops p cut
  let V := D.image (fun i => p i-i)
  let J := ∃ b,HigherAlignedTerminal p (height p a) b
  let EA : Finset (Fin n) := if J then {p z-z} else ∅
  have hEA : EA.card=(if J then 1 else 0) := by dsimp only [EA]; split_ifs <;> simp
  let E : Finset (Fin n) := {p 0,p 0-1} ∪ EA
  have hsub : M ∪ W ⊆ (Bad ∪ V) ∪ E := by
    intro t ht
    by_cases hex : t ∈ E
    · exact Finset.mem_union_right _ hex
    have hth : t ≠ p 0 := by intro he; exact hex (by simp [E,he])
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
      have hunpaid' : ¬ ∃ w : List Letter,p*eval w=1 ∧
          4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*(1 : ℕ) := by
        rintro ⟨w,hw,hprice⟩
        exact hunpaid ⟨w,hw,by omega⟩
      obtain ⟨i,hi,_,hib⟩ := minimum_unpaid_positive_backward p a b 1 (by omega) (by omega)
        hh hmin hb hunpaid' ht0 (by rwa [hbt])
      have hval : (p b-b).val=n-(b-p b).val := by
        have he : p b-b= -(b-p b) := by ring
        rw [he,Fin.val_neg,ite_eq_right (by intro heq; rw [heq,Fin.val_zero] at hgap; omega)]
      have hil : (p i-i).val < cut.val := by
        rw [hib,hval]
        change _ < (p 0-1).val
        have := (b-p b).isLt
        omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨hi,hil⟩,hib.trans hbt⟩)
    · have ht0 : t ≠ 0 := by intro he; exact hWzero (he ▸ htW)
      obtain ⟨g,hg,hgt⟩ := Finset.mem_image.mp htW
      have hg' := Finset.mem_Icc.mp hg
      rcases odd_full_terminal_threshold p a z g hn hh hmin hunpaid hz hg'.1 hg'.2 with
        hhigh | hhd | hprev | halign | ⟨b,hbd,_,hbh,hbr⟩
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        refine ⟨ht0,?_⟩
        apply Finset.mem_image.mpr
        refine ⟨-(g : Fin n)-(p a-a),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩,?_⟩
        rw [← hgt]; ring
      · exact False.elim (hex (by rw [← hgt,hhd]; simp [E]))
      · exact False.elim (hex (by rw [← hgt,hprev.1]; simp [E]))
      · have hJ : J := halign.2
        exact False.elim (hex (by rw [← hgt,halign.1]; simp [E,EA,hJ]))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨b,Finset.mem_filter.mpr ⟨hbd,hcutupper b hbh⟩,hbr.trans hgt⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (Bad ∪ V) E)
  have hMW := Finset.card_union_add_card_inter M W
  have hv : V.card ≤ D.card := Finset.card_image_le
  have hBV := Finset.card_union_le Bad V
  have hd := lower_offset_threshold_drop_bound p cut
  rw [ite_eq_right hcuthead,hcutheight] at hd
  change D.card+1 ≤ height p a+1 at hd
  have hE : E.card ≤ 2+EA.card := by
    have h1 := Finset.card_union_le ({p 0,p 0-1} : Finset (Fin n)) EA
    have h2 := Finset.card_pair_eq_one_or_two (a := p 0) (b := p 0-1)
    change E.card ≤ _ at h1
    omega
  have hexcess : secondExcess p a=(Z.card : ℤ)-P.card := by
    have he := second_excess_count p a hmin
    have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
    change 2*secondExcess p a=2*(Z.card : ℤ)-2*P.card+_ at he
    rw [hn'] at he
    nlinarith only [he]
  change secondExcess p a+1 ≤ ((if J then 1 else 0 : ℕ) : ℤ)
  rw [hexcess]
  omega

theorem odd_unpaid_terminal_head_aligned_bound (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (_hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    secondExcess p a+1 ≤
      ((if ∃ b,HigherAlignedTerminal p (height p a) b then 1 else 0 : ℕ) : ℤ) :=
  odd_unpaid_small_head_aligned_bound p a hn hh hmin hR hhead hg2 hunpaid

theorem odd_unpaid_terminal_head_zero_excess (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 3)
    (hhead : height p 0=height p a)
    (hg1 : 0 < (-p 0).val) (hg2 : (-p 0).val ≤ height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : secondExcess p a=0 := by
  have hb := odd_unpaid_terminal_head_aligned_bound p a hn hh hmin hR hhead hg1 hg2 hunpaid
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  split_ifs at hb <;> omega

#print axioms odd_unpaid_terminal_head_aligned_bound
#print axioms odd_unpaid_small_head_aligned_bound
#print axioms odd_unpaid_terminal_head_zero_excess
end LX.AnchoredPhases
