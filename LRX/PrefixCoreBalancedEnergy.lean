import LRX.ActualTwoComponentPeakGeometry

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual initial source core is an invariant union of cycles. -/
theorem prefix_source_core_invariant (p : State n) (i : Fin n) :
    p i ∈ prefixSourceCore p ↔ i ∈ prefixSourceCore p := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  simp only [prefixSourceCore,Finset.mem_filter]
  rw [source_packets_invariant,← zero_component_prefix,← zero_component_prefix]
  exact and_congr Iff.rfl (CycleFootprint.component_invariant hd 0 i)

/-- Original majorization bounds core energy by its active cardinality,
without requiring a separately majorized source permutation. -/
theorem prefix_core_balanced_energy_bound (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) :
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤
      (((prefixSourceCore p).card/2 : ℕ) : ℤ)*
        ((n : ℤ)-((prefixSourceCore p).card/2 : ℕ)) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hbal : (∑ i ∈ prefixSourceCore p, displacement p.symm i)=0 :=
    PrunedLift.canonical_balance p (prefixSourceCore p) (prefix_source_core_invariant p)
  exact AffineLift.balanced_subset_energy hd.1 hmaj (prefixSourceCore p) hbal

/-- A second actual density bound using the core's balanced support capacity. -/
theorem prefix_component_support_density_bound (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    2*(∑ i, |displacement p.symm i|) ≤
      2*(((prefixSourceCore p).card/2 : ℕ) : ℤ)*((n : ℤ)-((prefixSourceCore p).card/2 : ℕ))+
        ((areaWindowFamily p (componentSet p 0).card).map (fun A => (A.size : ℤ)^2)).sum := by
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  obtain ⟨hm,ha⟩ := area_window_family_spec p L hproper.le hcut
  have henergy := (window_family_selected_energy (areaWindowFamily p L) p.symm hm ha).2.2
  have hsplit := area_core_energy_partition p hc hproper
  have hcore := prefix_core_balanced_energy_bound p hmaj
  have hfixed : (0 : ℤ) ≤ ((familyPositions (areaWindowFamily p L) \
      Equiv.Perm.support p.symm).card : ℤ) := Int.natCast_nonneg _
  change 2*(∑ i, |displacement p.symm i|) ≤ _+
    ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
  change (∑ i, |displacement p.symm i|) =
    (∑ i ∈ familyPositions (areaWindowFamily p L), |displacement p.symm i|)+
      (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) at hsplit
  nlinarith only [henergy,hsplit,hcore,hfixed]

omit [NeZero n] in
/-- The canonical energy is twice an integer, by the exact cut-load sum. -/
theorem canonical_energy_twice (p : State n) :
    ∃ z : ℤ, (∑ i, |displacement p.symm i|)=2*z := by
  refine ⟨∑ e ∈ Finset.range (n+1), (halfLoad p.symm e : ℤ),?_⟩
  exact footrule p.symm

#print axioms prefix_core_balanced_energy_bound
#print axioms prefix_component_support_density_bound
#print axioms canonical_energy_twice
end LRX.FiniteCuts
