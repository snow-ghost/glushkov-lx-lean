import LX.OddAlignedObstruction
import LX.OddWideCutCount
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A minimum head and an unpaid aligned higher phase force the head
value to be exactly one. The argument uses the actual near-top prefix. -/
theorem rank_two_unpaid_aligned_minimum_head_geometry (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hhead : height p 0=height p a)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    p 0=1 ∧ (fixedPositions (permutation p b)).card=(b-p b).val := by
  classical
  let q := permutation p b
  let k := q 0
  let g := (b-p b).val
  let F := fixedPositions q
  let B := Finset.univ.filter fun i : Fin n => (cyclicOffset p b i).val < k.val
  let A := Finset.Ioo (0 : Fin n) k
  obtain ⟨hFpos,hFtwo,hFgap,hgap,hkpos,hkcap⟩ :=
    rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid
  have hkoff : cyclicOffset p b 0=k := by
    rw [cyclic_offset_normalized,sub_zero]
  rw [hkoff] at hkpos hkcap
  have hq0 : q 0 ≠ 0 := Fin.ne_of_val_ne (by change k.val ≠ 0; omega)
  have hheight := hb.1
  have hpre := odd_unpaid_aligned_prefix p (height p a) b hn (by omega) hb hunpaid
  have hforward := near_top_prefix_forward p b (g+1) (by omega) hq0
    (fun i hi => hpre i (by omega))
  have hBcard : B.card=k.val-1 := by
    have ht := reanchor_height p b 0
    rw [hkoff,hhead] at ht
    change (height p a : ℤ)=(height p b : ℤ)-(k.val : ℤ)+B.card at ht
    omega
  have hFB : F ⊆ B := by
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero]; omega⟩
  have hAF : A ⊆ F := by
    intro i hi
    have hi' := Finset.mem_Ioo.mp hi
    apply (mem_fixedPositions _ _).mpr
    exact (hforward 0 (by simp [g])).2 i hi'.1 hi'.2
  have hAcard : A.card=k.val-1 := by
    dsimp only [A]
    rw [Fin.card_Ioo,Fin.val_zero]
    omega
  have hBA : B=A := (Finset.eq_of_subset_of_card_le (hAF.trans hFB) (by omega)).symm
  have hFcard := Finset.card_le_card hFB
  have hk2 : 2 ≤ k.val := by change F.card ≥ 1 at hFpos; omega
  have hkgt : g < k.val := by
    by_contra hnot
    have hfk := hforward k (by omega)
    have hqkne : q k ≠ k := by
      intro he
      have hz : k=0 := q.injective he
      have hv := congrArg Fin.val hz
      rw [Fin.val_zero] at hv
      omega
    have hqkgt : k.val < (q k).val := by
      have hle : k.val ≤ (q k).val := hfk.1
      have hvne : (q k).val ≠ k.val := fun he => hqkne (Fin.ext he)
      omega
    have hkn : k.val+1 < n := by have := (q k).isLt; omega
    let j : Fin n := ⟨k.val+1,hkn⟩
    have hqkval : (q k).val=k.val+1 := by
      by_contra hne
      have hjfix : q j=j := hfk.2 j (by change k.val < k.val+1; omega)
        (by change k.val+1 < (q k).val; omega)
      have hjA : j ∈ A := hBA ▸ hFB ((mem_fixedPositions _ _).mpr hjfix)
      have hjlt := (Finset.mem_Ioo.mp hjA).2
      change k.val+1 < k.val at hjlt
      omega
    have hoffk : (cyclicOffset p b k).val=1 := by
      rw [cyclic_offset_normalized,Fin.coe_sub_iff_le.mpr hfk.1]
      change (q k).val-k.val=1
      omega
    have hkB : k ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hoffk]; omega⟩
    have hkA : k ∈ A := hBA ▸ hkB
    have hkk := (Finset.mem_Ioo.mp hkA).2
    exact (lt_irrefl k) hkk
  have hkg : k.val=g+1 := by
    change k.val ≤ F.card+1 at hkcap
    change F.card ≤ g at hFgap
    omega
  have he : p 0=k-(b-p b) := by
    change p 0=(p 0+(b-p b))-(b-p b)
    ring
  have hv : (k-(b-p b)).val=1 := by
    rw [Fin.coe_sub_iff_le.mpr (show b-p b ≤ k by change g ≤ k.val; omega)]
    change k.val-g=1
    omega
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  refine ⟨he.trans (Fin.ext (hv.trans hv1.symm)),?_⟩
  change F.card=g
  change F.card ≤ g at hFgap
  change k.val ≤ F.card+1 at hkcap
  omega

theorem rank_two_unpaid_aligned_minimum_head (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hhead : height p 0=height p a)
    (hb : HigherAlignedTerminal p (height p a) b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=1 :=
  (rank_two_unpaid_aligned_minimum_head_geometry p a b hn hh hR hhead hb hunpaid).1

theorem rank_two_unpaid_minimum_head_no_smaller (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hhead : height p 0=height p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ¬ SmallerHigherAlignedTerminal p (height p a) := by
  rintro ⟨b,c,hb,hch,hcg,hcb⟩
  have hF := (rank_two_unpaid_aligned_minimum_head_geometry p a b hn hh hR hhead hb hunpaid).2
  have hoff : (cyclicOffset p b c).val=(b-p b).val-(c-p c).val := by
    have he : cyclicOffset p b c=(b-p b)-(c-p c) := by unfold cyclicOffset; ring
    rw [he,Fin.coe_sub_iff_le.mpr (show c-p c ≤ b-p b from Nat.le_of_lt hcb)]
  have hbelow : (fixedPositions (permutation p b)).card ≤ belowCount p b (cyclicOffset p b c).val := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p b i).mpr ((mem_fixedPositions _ _).mp hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz,Fin.val_zero,hoff]; omega⟩
  have ht := reanchor_height p b c
  have hbh := hb.1
  rw [hch,hbh] at ht
  omega

#print axioms rank_two_unpaid_aligned_minimum_head
#print axioms rank_two_unpaid_minimum_head_no_smaller
end LX.AnchoredPhases
