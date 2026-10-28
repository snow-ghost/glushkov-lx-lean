import LX.NearTopPrefixBound
import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- In a near-top prefix, an image cannot pass the first position beyond
all fixed positions. This bounds each tail offset by the remaining prefix. -/
theorem near_top_prefix_tail_offset (p : State n) (a : Fin n) (G : ℕ)
    (hh : 2 ≤ height p a) (hhead : permutation p a 0 ≠ 0)
    (hfix : ∀ i : Fin n,permutation p a i=i → i.val ≤ G)
    (hpre : ∀ i : Fin n,i.val ≤ G → height p a-1 ≤ backwardDepth (displacement p a) i)
    (i : Fin n) (hi : i.val ≤ G) :
    (cyclicOffset p a i).val ≤ G+1-i.val := by
  have hp := near_top_prefix_forward p a (G+1) hh hhead (fun j hj => hpre j (by omega))
  have hpi := hp i (by omega)
  have himg : (permutation p a i).val ≤ G+1 := by
    by_contra hn
    have hgn : G+1 < n := by have := (permutation p a i).isLt; omega
    let j : Fin n := ⟨G+1,hgn⟩
    have hjfix := hpi.2 j (by change i.val < G+1; omega) (by change G+1 < _; omega)
    have hj := hfix j hjfix
    change G+1 ≤ G at hj
    omega
  rw [cyclic_offset_normalized,Fin.coe_sub_iff_le.mpr (show i ≤ permutation p a i from hpi.1)]
  omega

/-- Among two nonhead phases of equal height with cheap finishes, the
larger gap has an early low-depth position. No rank-peak bound is needed. -/
theorem paired_aligned_early_low_depth (p : State n) (a b : Fin n)
    (hh : 2 ≤ height p a) (hheight : height p b=height p a)
    (hheada : p 0 ≠ p a-a) (hheadb : p 0 ≠ p b-b)
    (hlasta : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hlastb : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hfa : a.val+(-p a).val=(a-p a).val)
    (hfb : b.val+(-p b).val=(b-p b).val)
    (hgb : 0 < (b-p b).val) (hgap : (b-p b).val < (a-p a).val) :
    ∃ i : Fin n,backwardDepth (displacement p a) i < height p a-1 ∧
      i.val ≤ (a-p a).val := by
  classical
  by_contra hnone
  let G := (a-p a).val
  let V := (b-p b).val
  let t := G-V
  have hpre (i : Fin n) (hi : i.val ≤ G) : height p a-1 ≤ backwardDepth (displacement p a) i := by
    by_contra hd
    exact hnone ⟨i,by omega,hi⟩
  have hhead : permutation p a 0 ≠ 0 := by
    intro he
    apply hheada
    change p 0+(a-p a)=0 at he
    linear_combination he
  have hfix (i : Fin n) (hi : permutation p a i=i) : i.val ≤ G := by
    have hr : p i-i=p a-a := by
      change p i+(a-p a)=i at hi
      linear_combination hi
    have hb := hlasta i hr
    omega
  have hoffval : (cyclicOffset p a b).val=t := by
    have he : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
    rw [he,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hgap.le)]
  have hcount : belowCount p a t=t := by
    have he := reanchor_height p a b
    rw [hoffval,hheight] at he
    omega
  let A := Finset.univ.filter fun i : Fin n => (cyclicOffset p a i).val < t
  let T := Finset.Ioc (b-p b) (a-p a)
  have hT : T.card=t := by dsimp only [T,t,G,V]; rw [Fin.card_Ioc]
  have hA : A.card=t := hcount
  have hsub : T ⊆ A := by
    intro i hi
    have hi' := Finset.mem_Ioc.mp hi
    have hil : V < i.val := hi'.1
    have hir : i.val ≤ G := hi'.2
    have hbnd := near_top_prefix_tail_offset p a G hh hhead hfix hpre i hir
    have hle : (cyclicOffset p a i).val ≤ t := by omega
    have hne : (cyclicOffset p a i).val ≠ t := by
      intro he
      have hoff : cyclicOffset p a i=cyclicOffset p a b := Fin.ext (by omega)
      have hbi : permutation p b i=i := by
        apply (offset_zero_iff_source_fixed p b i).mp
        rw [cyclic_offset_reanchor p a b i,hoff,sub_self]
      have hr : p i-i=p b-b := by
        change p i+(b-p b)=i at hbi
        linear_combination hbi
      have hib := hlastb i hr
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have heq : A=T := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hzero : (0 : Fin n) ∉ A := by rw [heq]; simp [T]
  have hheadlo : t ≤ (cyclicOffset p a 0).val := by
    by_contra he
    exact hzero (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
  have hheadne : (cyclicOffset p a 0).val ≠ t := by
    intro he
    have hoff : cyclicOffset p a 0=cyclicOffset p a b := Fin.ext (by omega)
    have hz : cyclicOffset p b 0=0 := by rw [cyclic_offset_reanchor p a b 0,hoff,sub_self]
    apply hheadb
    simpa only [cyclicOffset,sub_zero,sub_eq_zero] using hz
  have hn1 : 1 < n := by have := (a-p a).isLt; omega
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt hn1]
  have hq0 : (permutation p a 0).val=(cyclicOffset p a 0).val := by
    rw [cyclic_offset_normalized,sub_zero]
  have hp := near_top_prefix_forward p a (G+1) hh hhead (fun j hj => hpre j (by omega))
  have hfix1 : permutation p a 1=1 := (hp 0 (by simp)).2 1
    (by simp only [Fin.val_zero,hv1]; omega) (by rw [hv1]; omega)
  have hoff1 : cyclicOffset p a 1=0 := (offset_zero_iff_source_fixed p a 1).mpr hfix1
  have hmem : (1 : Fin n) ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hoff1,Fin.val_zero]
    omega
  rw [heq] at hmem
  have hv := (Finset.mem_Ioc.mp hmem).1
  change (b-p b).val < (1 : Fin n).val at hv
  omega

#print axioms near_top_prefix_tail_offset
#print axioms paired_aligned_early_low_depth
end LX.AnchoredPhases
