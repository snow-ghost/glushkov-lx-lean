import LX.OddHigherHead
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

private theorem forward_prefix_unit_step (q : State n) (r : ℕ)
    (hf : LX.FiniteDropBudget.ForwardPrefix q r) (i : Fin n) (hi : i.val < r)
    (himove : q i ≠ i) (hafter : ∀ j : Fin n,i.val < j.val → q j ≠ j) :
    (q i).val=i.val+1 := by
  have hfi := hf i hi
  have hne : (q i).val ≠ i.val := fun he => himove (Fin.ext he)
  have hgt : i.val < (q i).val := by omega
  by_contra hnot
  let j : Fin n := ⟨i.val+1,by have := (q i).isLt; omega⟩
  exact hafter j (by change i.val < i.val+1; omega)
    (hfi.2 j (by change i.val < i.val+1; omega) (by change i.val+1 < (q i).val; omega))

/-- In an unpaid aligned phase the fixed-fiber size equals the image
of the moving head. A smaller fiber would force two extra unit arrows
below the head's rank threshold. -/
theorem rank_two_unpaid_aligned_head_fiber (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    (fixedPositions (permutation p b)).card=(cyclicOffset p b 0).val := by
  classical
  let q := permutation p b
  let k := q 0
  let g := (b-p b).val
  let F := fixedPositions q
  let B := Finset.univ.filter fun i : Fin n => (cyclicOffset p b i).val < k.val
  let A := Finset.Ioo (0 : Fin n) k
  obtain ⟨hFpos,hFtwo,hFgap,hgap,hkpos,hkcap⟩ :=
    rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  obtain ⟨hhead,hdpos,_⟩ := rank_two_unpaid_higher_head p a hn hh hmin hR hunpaid
  obtain ⟨hdg,hkg⟩ := rank_two_unpaid_head_before_aligned_finish p a b hn hh hmin hR hb hunpaid
  have hkoff : cyclicOffset p b 0=k := by rw [cyclic_offset_normalized,sub_zero]
  rw [hkoff] at hkpos hkcap hkg ⊢
  change F.card=k.val
  change 1 ≤ F.card at hFpos
  change F.card ≤ 2 at hFtwo
  change k.val ≤ F.card+1 at hkcap
  have hheight := hb.1
  have hq0 : q 0 ≠ 0 := Fin.ne_of_val_ne (by change k.val ≠ 0; omega)
  have hpre := odd_unpaid_aligned_prefix p (height p a) b hn (by omega) hb hunpaid
  have hf := near_top_prefix_forward p b (g+1) (by omega) hq0
    (fun i hi => hpre i (by omega))
  have hBcard : B.card=k.val := by
    have ht := reanchor_height p b 0
    rw [hkoff,hhead,hheight] at ht
    change _= _-(k.val : ℤ)+B.card at ht
    omega
  have hFB : F ⊆ B := by
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  have hAF : A ⊆ F := by
    intro i hi
    have hi' := Finset.mem_Ioo.mp hi
    exact (mem_fixedPositions _ _).mpr ((hf 0 (by simp [g])).2 i hi'.1 hi'.2)
  have hAcard : A.card=k.val-1 := by dsimp only [A]; rw [Fin.card_Ioo,Fin.val_zero]; omega
  have hFle := (Finset.card_le_card hFB).trans_eq hBcard
  by_contra hne
  have hAFcard := Finset.card_le_card hAF
  have hFA : F=A := (Finset.eq_of_subset_of_card_le hAF (by omega)).symm
  have hfixlt (i : Fin n) (hi : q i=i) : i.val < k.val := by
    have hiA : i ∈ A := hFA ▸ (mem_fixedPositions _ _).mpr hi
    exact (Finset.mem_Ioo.mp hiA).2
  have hk2 : 2 ≤ k.val := by omega
  have hk3 : k.val ≤ 3 := by omega
  let j : Fin n := ⟨k.val+1,by omega⟩
  have hkmove : q k ≠ k := by intro he; have := hfixlt k he; omega
  have hjmove : q j ≠ j := by intro he; have := hfixlt j he; change k.val+1 < k.val at this; omega
  have hkstep : (q k).val=k.val+1 := forward_prefix_unit_step q (g+1) hf k
    (by dsimp only [g]; omega) hkmove (by intro i hi he; have := hfixlt i he; omega)
  have hjstep : (q j).val=j.val+1 := forward_prefix_unit_step q (g+1) hf j
    (by change k.val+1 < g+1; dsimp only [g]; omega) hjmove
    (by intro i hi he; have := hfixlt i he; change k.val+1 < i.val at hi; omega)
  have hunit (i : Fin n) (hs : (q i).val=i.val+1) : (cyclicOffset p b i).val=1 := by
    rw [cyclic_offset_normalized,Fin.coe_sub_iff_le.mpr (show i ≤ q i by omega)]
    change (q i).val-i.val=1
    omega
  have hkB : k ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hunit k hkstep]; omega⟩
  have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hunit j hjstep]; omega⟩
  have hkj : k ≠ j := by intro he; have := congrArg Fin.val he; change k.val=k.val+1 at this; omega
  have hkF : k ∉ F := fun hi => hkmove ((mem_fixedPositions _ _).mp hi)
  have hjF : j ∉ F := fun hi => hjmove ((mem_fixedPositions _ _).mp hi)
  have hc := Finset.card_le_card (Finset.insert_subset hkB (Finset.insert_subset hjB hFB))
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert] using not_or_intro hkj hkF),
    Finset.card_insert_of_notMem hjF,hBcard] at hc
  omega

/-- The last fixed position lies beyond the head offset, while the
head's own gap is at most two. -/
theorem rank_two_unpaid_aligned_source_after_head_offset (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    (cyclicOffset p b 0).val < b.val ∧ (-p 0).val ≤ 2 := by
  classical
  have hF := rank_two_unpaid_aligned_head_fiber p a b hn hh hmin hR hb hunpaid
  obtain ⟨_,_,hFg,hg,hkpos,_⟩ := rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  obtain ⟨hdg,hkg⟩ := rank_two_unpaid_head_before_aligned_finish p a b hn hh hmin hR hb hunpaid
  have hsub : fixedPositions (permutation p b) ⊆ Finset.Ioc (0 : Fin n) b := by
    intro i hi
    have hi' := (mem_fixedPositions _ _).mp hi
    have hraw : p i-i=p b-b := by change p i+(b-p b)=i at hi'; linear_combination hi'
    have hi0 : i ≠ 0 := by intro he; subst i; exact hb.2.1 (by simpa only [sub_zero] using hraw)
    exact Finset.mem_Ioc.mpr ⟨Fin.pos_iff_ne_zero.mpr hi0,hb.2.2.1 i hraw⟩
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ioc,Fin.val_zero,Nat.sub_zero,hF] at hc
  have hne : (cyclicOffset p b 0).val ≠ b.val := by
    intro he
    have he' : permutation p b 0=b := by
      rw [cyclic_offset_normalized,sub_zero] at he
      exact Fin.ext he
    have hb0 : b=0 := (permutation p b).injective ((permutation_anchor p b).trans he'.symm)
    have hbval : b.val=0 := by rw [hb0,Fin.val_zero]
    omega
  rw [hF] at hg
  exact ⟨by omega,by omega⟩

#print axioms rank_two_unpaid_aligned_head_fiber
#print axioms rank_two_unpaid_aligned_source_after_head_offset
end LX.AnchoredPhases
