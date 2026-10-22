import LRX.FiniteWeightedPacketFamily
import LRX.JoinedCoreEnergy

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_selected_peak_family (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r port : Fin n) (hr : r ∈ sourcePackets p) (hport : port=r ∨ port+1=r)
    (cycles : List (State n)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ fillingCycles p)
    (ss : List (ExactService n))
    (hst : ss.map (fun s => s.service.target)=cycles.map (fun q => q⁻¹))
    (hcan : CanonicalFamily ss)
    (hprice : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ)) :
    ∃ a : ExactService n, a.service.port=port ∧
      CanonicalFamily (a::ss) ∧
      (a::ss).Pairwise (fun s t => s.service.target.Disjoint t.service.target) ∧
      ((a::ss).map (fun s => s.service.target)).prod=joinedComponents p hc ∧
      (((a::ss).map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ) ≤
        (∑ i, |displacement p.symm i|)+2*(bridgeBudget (componentBridges p hc) : ℤ)-
          portLoad (displacement (joinedComponents p hc).symm) port-
          (cycles.map (fun q => 2*(leftPeak q n : ℤ))).sum := by
  classical
  let G := joinedComponents p hc
  have hfactor (q : State n) (hq : q ∈ cycles) : q ∈ (G⁻¹).cycleFactorsFinset := by
    have hh := hout q hq
    rw [← joined_outside_cycles p hc hk] at hh
    exact (Finset.mem_filter.mp hh).1
  have hcy (q : State n) (hq : q ∈ cycles) : q.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hfactor q hq)).1
  let selected := (cycles.map (fun q => q⁻¹)).prod
  have hsdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_map.mp
    rw [hst]
    exact inverse_targets_disjoint cycles hdis
  have ht : (ss.map (fun a => a.service.target)).prod=selected := by rw [hst]
  have hpart : CyclePart.IsPart selected G := by
    apply CyclePart.product _ G (inverse_targets_disjoint cycles hdis)
    intro t ht
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    simpa only [inv_inv] using CyclePart.inverse (CyclePart.cycle_factor (hfactor q hq))
  have hkeep : PrunedLift.KeepsCore G (displacement G.symm) r selected.supportᶜ := by
    intro i hri hir
    have hiT := joined_source_packets_predecessor_closed p hc hir hr
    apply Finset.mem_compl.mpr
    intro hi
    obtain ⟨t,ht,hit⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    have hiq : i ∈ q.support := by simpa only [Equiv.Perm.support_inv] using hit
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp (hout q hq)).2 hiq hiT
  have hrm : G.symm r ≠ r := by
    apply (mem_support_inverse _ r).mp
    change r ∈ (bridgeSequence p (componentBridges p hc)).support
    rw [bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)]
    exact (mem_support_inverse p r).mpr ((mem_source_packets p r).mp hr).1
  obtain ⟨a,ha,hcanonical,hpair,hprod,hrot⟩ := finite_weighted_packet_family hn G selected r port hrm hport
    (joined_packet_cover_at_source p hc hk r hr) hpart hkeep ss hsdis hcan ht
    (fun s => 2*(leftPeak s.service.target⁻¹ n : ℤ)) (fun s hs => le_of_eq (hprice s hs))
  have hsave : ss.map (fun s => 2*(leftPeak s.service.target⁻¹ n : ℤ))=
      cycles.map (fun q => 2*(leftPeak q n : ℤ)) := by
    have hh := congrArg (List.map (fun q : State n => 2*(leftPeak q⁻¹ n : ℤ))) hst
    simpa only [List.map_map,Function.comp_def,inv_inv] using hh
  rw [hsave] at hrot
  have hm := (joined_components_prices p hc).2.1
  exact ⟨a,ha,hcanonical,hpair,hprod,by dsimp [G] at hrot; omega⟩

theorem joined_peak_packet_family (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r : Fin n) (hr : r ∈ sourcePackets p)
    (cycles : List (State n)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ fillingCycles p) :
    ∃ (ss : List (ExactService n)) (a : ExactService n),
      ss.map (fun s => s.service.target)=cycles.map (fun q => q⁻¹) ∧ a.service.port=r ∧
      CanonicalFamily (a::ss) ∧
      (a::ss).Pairwise (fun s t => s.service.target.Disjoint t.service.target) ∧
      ((a::ss).map (fun s => s.service.target)).prod=joinedComponents p hc ∧
      (((a::ss).map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ) ≤
        (∑ i, |displacement p.symm i|)+2*(bridgeBudget (componentBridges p hc) : ℤ)-
          portLoad (displacement (joinedComponents p hc).symm) r-
          (cycles.map (fun q => 2*(leftPeak q n : ℤ))).sum := by
  have hcy (q : State n) (hq : q ∈ cycles) : q.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (Finset.mem_filter.mp (hout q hq)).1).1
  obtain ⟨ss,hst,hcan,hprice⟩ := global_peak_service_family hn cycles hcy
  obtain ⟨a,ha,hcanonical,hpair,hprod,hrot⟩ :=
    joined_selected_peak_family hn p hc hk r r hr (Or.inl rfl) cycles hdis hout ss hst hcan hprice
  exact ⟨ss,a,hst,ha,hcanonical,hpair,hprod,hrot⟩

#print axioms joined_peak_packet_family
end LRX.FiniteCuts
