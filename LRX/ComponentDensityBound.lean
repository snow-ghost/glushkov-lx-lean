import LRX.PrefixCoreEnergy
import LRX.LargeComponentPeakCapacity

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- All original energy splits into actual selected intervals and the original prefix core. -/
theorem area_core_energy_partition (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    (∑ i, |displacement p.symm i|) =
      (∑ i ∈ familyPositions (areaWindowFamily p (componentSet p 0).card), |displacement p.symm i|) +
      (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) := by
  classical
  have hdis : Disjoint (prefixSourceCore p) (isolatedVertices p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hs := (mem_source_packets p i).mp (Finset.mem_filter.mp hi).1
    have he := isolated_vertex_fixed p i hj
    apply hs.1
    apply p.injective
    simpa only [Equiv.apply_symm_apply] using he.symm
  have hzero : (∑ i ∈ isolatedVertices p, |displacement p.symm i|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have he := isolated_vertex_fixed p i hi
    have hf : p.symm i = i := by
      apply p.injective
      simpa only [Equiv.apply_symm_apply] using he.symm
    simp only [displacement,hf,sub_self,abs_zero]
  have h := Finset.sum_add_sum_compl
    (familyPositions (areaWindowFamily p (componentSet p 0).card))
    (fun i => |displacement p.symm i|)
  rw [area_positions_complement p hc hproper,Finset.sum_union hdis,hzero,add_zero] at h
  exact h.symm

/-- C10 for a real large initial component and the real global source peak. -/
theorem prefix_component_density_bound (p : State n)
    (hlarge : (n+1)/2 < (componentSet p 0).card)
    (hproper : (componentSet p 0).card < n) :
    let L := (componentSet p 0).card
    let U := sourceHalfPeak p
    let As := areaWindowFamily p L
    2*(∑ i, |displacement p.symm i|) ≤
      4*(U : ℤ)*((L : ℤ)-U)+(As.map (fun A => (A.size : ℤ)^2)).sum := by
  have hn := NeZero.pos n
  have hc : 2 ≤ (componentSet p 0).card := by omega
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  have hwidth := large_component_source_peak_capacity p 0 hlarge
  have hcore := prefix_core_energy_bound p hwidth
  obtain ⟨hm,ha⟩ := area_window_family_spec p L hproper.le hcut
  have henergy := (window_family_selected_energy (areaWindowFamily p L) p.symm hm ha).2.2
  have hsplit := area_core_energy_partition p hc hproper
  dsimp only at ⊢
  change 2*(∑ i, |displacement p.symm i|) ≤
    4*(sourceHalfPeak p : ℤ)*((L : ℤ)-sourceHalfPeak p)+
      ((areaWindowFamily p L).map (fun A => (A.size : ℤ)^2)).sum
  change (∑ i, |displacement p.symm i|) =
    (∑ i ∈ familyPositions (areaWindowFamily p L), |displacement p.symm i|)+
    (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) at hsplit
  change (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤
    2*(sourceHalfPeak p : ℤ)*((L : ℤ)-sourceHalfPeak p) at hcore
  have hf : (0 : ℤ) ≤ ((familyPositions (areaWindowFamily p L) \
      Equiv.Perm.support p.symm).card : ℤ) := by positivity
  nlinarith

/-- C10 at the derived zero cut of any original large proper component. -/
theorem component_density_bound (p : State n) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (hproper : (componentSet p root).card < n) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let U := sourceHalfPeak q
    let As := areaWindowFamily q L
    2*(∑ i, |displacement q.symm i|) ≤
      4*(U : ℤ)*((L : ℤ)-U)+(As.map (fun A => (A.size : ℤ)^2)).sum := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hzero : (componentSet q 0).card = (componentSet p root).card := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    have he : componentSet p root = componentSet p r :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card = (componentSet p r).card at h
    rwa [← he] at h
  have h := prefix_component_density_bound q (by omega) (by omega)
  dsimp only at h ⊢
  rw [hzero] at h
  exact h

#print axioms area_core_energy_partition
#print axioms prefix_component_density_bound
#print axioms component_density_bound
end LRX.FiniteCuts
