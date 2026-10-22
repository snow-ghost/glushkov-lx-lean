import LRX.JoinedPeakArcPorts

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

noncomputable def fillingHalfPeakSum (p : State n) : ℤ :=
  ((fillingCycles p).toList.map (fun q => (leftPeak q n : ℤ))).sum

theorem filling_peak_arc_families (hn : 2 ≤ n) (p : State n) (start finish : Fin n)
    (hne : start ≠ finish) :
    ∃ (cycles : Bool → List (State n)) (services : Bool → List (ExactService n)),
      (∀ dir, (cycles dir).Pairwise Equiv.Perm.Disjoint) ∧
      (∀ dir q, q ∈ cycles dir → q ∈ fillingCycles p) ∧
      (∀ dir, (services dir).map (fun s => s.service.target)=(cycles dir).map (fun q => q⁻¹)) ∧
      (∀ dir, CanonicalFamily (services dir)) ∧
      (∀ dir a, a ∈ services dir → (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ)) ∧
      (∀ dir a, a ∈ services dir → (arcCoordinate dir start a.service.port).val ≤
        (arcCoordinate dir start finish).val) ∧
      ((cycles true).map (fun q => 2*(leftPeak q n : ℤ))).sum+
        ((cycles false).map (fun q => 2*(leftPeak q n : ℤ))).sum=2*fillingHalfPeakSum p := by
  classical
  let all := (fillingCycles p).toList
  have hmem (q : State n) (hq : q ∈ all) : q ∈ fillingCycles p := Finset.mem_toList.mp hq
  have hcy (q : State n) (hq : q ∈ all) : q.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp (hmem q hq)).1).1
  have hdis : all.Pairwise Equiv.Perm.Disjoint := by
    apply (Finset.nodup_toList _).imp_of_mem
    intro a b ha hb hab
    exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint (p⁻¹))
      (Finset.mem_filter.mp (hmem a ha)).1 (Finset.mem_filter.mp (hmem b hb)).1 hab
  obtain ⟨ss,hst,hcan,hprice⟩ := global_peak_service_family hn all hcy
  have hsdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_map.mp
    rw [hst]
    exact inverse_targets_disjoint all hdis
  let selected := peakArcServices start finish ss
  let cycles := fun dir => (selected dir).map (fun a => a.service.target⁻¹)
  have ht (dir) : (selected dir).map (fun s => s.service.target)=(cycles dir).map (fun q => q⁻¹) := by
    simp [cycles]
  have hcdis (dir) : (cycles dir).Pairwise Equiv.Perm.Disjoint := by
    have hh := inverse_targets_disjoint ((selected dir).map (fun a => a.service.target))
      (List.pairwise_map.mpr (peak_arc_services_disjoint start finish ss hsdis dir))
    simpa only [List.map_map,Function.comp_def] using hh
  have hcmem (dir) (q : State n) (hq : q ∈ cycles dir) : q ∈ fillingCycles p := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    have hsa := peak_arc_services_mem start finish ss dir ha
    have hh : a.service.target ∈ ss.map (fun a => a.service.target) := List.mem_map.mpr ⟨a,hsa,rfl⟩
    rw [hst] at hh
    obtain ⟨c,hc,he⟩ := List.mem_map.mp hh
    rw [← he,inv_inv]
    exact hmem c hc
  refine ⟨cycles,selected,hcdis,hcmem,ht,
    fun dir => peak_arc_services_canonical start finish ss hcan dir,
    fun dir a ha => hprice a (peak_arc_services_mem start finish ss dir ha),
    fun dir a ha => peak_arc_services_range start finish hne ss dir a ha,?_⟩
  have hs := peak_arc_services_savings start finish ss (fun a => 2*(leftPeak a.service.target⁻¹ n : ℤ))
  have he : ss.map (fun a => 2*(leftPeak a.service.target⁻¹ n : ℤ))=
      all.map (fun q => 2*(leftPeak q n : ℤ)) := by
    have hh := congrArg (List.map (fun q : State n => 2*(leftPeak q⁻¹ n : ℤ))) hst
    simpa only [List.map_map,Function.comp_def,inv_inv] using hh
  rw [he] at hs
  have hm : ∀ xs : List (State n), (xs.map (fun q => 2*(leftPeak q n : ℤ))).sum=
      2*(xs.map (fun q => (leftPeak q n : ℤ))).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons q rest ih => simp [ih,mul_add]
  rw [hm] at hs
  simpa only [cycles,selected,List.map_map,Function.comp_def,all,fillingHalfPeakSum] using hs

#print axioms filling_peak_arc_families
end LRX.FiniteCuts
