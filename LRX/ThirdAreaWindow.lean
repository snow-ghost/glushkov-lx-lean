import LRX.ActualWindowEnvelope
import LRX.ActualPeakSupportBound

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- If the original core does not fill the initial component, an actual internal window is nonempty. -/
theorem smaller_core_nonempty_internal_window (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n)
    (hR : (prefixSourceCore p).card < (componentSet p 0).card) :
    ∃ A ∈ positiveSourceFamily p (componentSet p 0).card, 0 < A.size := by
  classical
  let L := (componentSet p 0).card
  have hsub : prefixSourceCore p ⊆ left L := by
    intro i hi
    exact (mem_left L i).mpr (Finset.mem_filter.mp hi).2
  have hpos : 0 < (left L \ prefixSourceCore p).card := by
    rw [Finset.card_sdiff_of_subset hsub,left_card L hproper.le]
    exact Nat.sub_pos_of_lt hR
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hi,hnot⟩ := Finset.mem_sdiff.mp hi
  have hip : i.val < L := (mem_left L i).mp hi
  have hsource : i ∉ sourcePackets p := fun hs => hnot (Finset.mem_filter.mpr ⟨hs,hip⟩)
  obtain ⟨A,hA,hiA⟩ := (mem_family_positions _ _).mp
    (prefix_non_source_in_area_family p hc hproper i hip hsource)
  rcases List.mem_append.mp hA with hA | hA
  · refine ⟨A,hA,?_⟩
    unfold Contains at hiA
    omega
  · have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
      simpa only [Equiv.symm_symm] using canonical_lift p.symm
    have hcut (j : Fin n) : (p j).val < L ↔ j.val < L := by
      change (p j).val < (componentSet p 0).card ↔ j.val < (componentSet p 0).card
      rw [← zero_component_prefix,← zero_component_prefix]
      exact CycleFootprint.component_invariant hd 0 j
    have hb := (suffix_component_family_spec p L hproper.le hcut).2.2 A hA
    unfold Contains at hiA
    omega

/-- The third nonempty interval required by the t=2 envelope is extracted
from the all-size support bound, using the unpaid epsilon and peak bounds. -/
theorem two_component_three_nonempty_windows (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n)
    (ht : (nontrivialSuffixComponents p (componentSet p 0).card).card=2)
    (hm : 200 ≤ n/2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) ≤ 12)
    (hU : sourceHalfPeak p ≤ 7) :
    3 ≤ ((areaWindowFamily p (componentSet p 0).card).filter
      (fun A => decide (1 ≤ A.size))).length := by
  classical
  let L := (componentSet p 0).card
  have hc : 2 ≤ (componentSet p 0).card := by omega
  have hr := actual_peak_support_bound p hmaj hlarge hproper (by omega) (by rw [ht]; simpa using he)
  have hR : (prefixSourceCore p).card < (componentSet p 0).card := by omega
  obtain ⟨A,hA,hpos⟩ := smaller_core_nonempty_internal_window p hc hproper hR
  have hin : 1 ≤ ((positiveSourceFamily p L).filter (fun A => decide (1 ≤ A.size))).length := by
    have hmem : A ∈ (positiveSourceFamily p L).filter (fun A => decide (1 ≤ A.size)) :=
      List.mem_filter.mpr ⟨hA,by simp only [decide_eq_true_eq]; omega⟩
    exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
  have hf : (suffixComponentFamily p L).filter (fun A => decide (1 ≤ A.size)) =
      suffixComponentFamily p L := by
    apply List.filter_eq_self.mpr
    intro B hB
    have hh := suffix_family_sizes_nontrivial p L B hB
    simp only [decide_eq_true_eq]
    omega
  have hout : (suffixComponentFamily p L).length=2 := by
    simp only [suffixComponentFamily,List.length_map,Finset.length_toList,Finset.card_attach]
    exact ht
  change 3 ≤ ((positiveSourceFamily p L ++ suffixComponentFamily p L).filter
    (fun A => decide (1 ≤ A.size))).length
  rw [List.filter_append,List.length_append,hf,hout]
  omega

#print axioms smaller_core_nonempty_internal_window
#print axioms two_component_three_nonempty_windows
end LRX.FiniteCuts
