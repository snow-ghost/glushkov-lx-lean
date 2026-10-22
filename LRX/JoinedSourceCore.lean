import LRX.FiniteSourcePackets

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem joined_component_cross_reverse (p : State n) (hc : (componentRoots p).card=k+1) (i : Fin k) :
    FiniteReach (joinedComponents p hc) (bridgeEndpoints p hc i).2 (bridgeEndpoints p hc i).1 :=
  (bridge_sequence_cross_reach p _ (component_bridges_valid p hc)
    (component_bridges_separated p hc) _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).2

theorem joined_component_chain_reverse (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (i : Fin k) : FiniteReach (joinedComponents p hc)
      (bridgeEndpoints p hc i).2 (bridgeEndpoints p hc ⟨0,hk⟩).1 := by
  have h : ∀ t (ht : t < k), FiniteReach (joinedComponents p hc)
      (bridgeEndpoints p hc ⟨t,ht⟩).2 (bridgeEndpoints p hc ⟨0,hk⟩).1 := by
    intro t
    induction t with
    | zero => intro ht; exact joined_component_cross_reverse p hc ⟨0,ht⟩
    | succ t ih =>
      intro ht
      let a : Fin k := ⟨t,by omega⟩
      let b : Fin k := ⟨t+1,ht⟩
      have he : a.succ=b.castSucc := Fin.ext rfl
      have hm := ((mem_source_packets p _).mp (bridge_endpoints_in_source_packets p hc a).2).1
      have hp : CycleFootprint.LoadPath (displacement p.symm) (componentOrder p hc b.castSucc)
          (bridgeEndpoints p hc a).2 := by
        rw [← he]
        exact component_left_path p _
      exact ((joined_component_cross_reverse p hc b).trans
        (joined_component_right_reaches p hc b _ hm hp)).trans (ih a.isLt)
  exact h i.val i.isLt

theorem source_vertex_reaches_joined_root (p : State n) (hc : (componentRoots p).card=k+1)
    (hk : 0 < k) (x : Fin n) (hx : x ∈ sourcePackets p) :
    FiniteReach (joinedComponents p hc) x (bridgeEndpoints p hc ⟨0,hk⟩).1 := by
  obtain ⟨hxm,hxs⟩ := (mem_source_packets p x).mp hx
  obtain ⟨a,ha,hpath⟩ := component_roots_cover p x hxm
  obtain ⟨j,hj⟩ := component_order_surjective p hc a ha
  rw [← hj] at hpath
  by_cases hz : j.val=0
  · let i : Fin k := ⟨0,hk⟩
    have hij : j=i.castSucc := Fin.ext hz
    rw [hij] at hpath
    have hv := ordered_component_bridge_valid p hc i
    have hm := ((mem_source_packets p _).mp (bridge_endpoints_in_source_packets p hc i).1).1
    have hp : FiniteReach p (bridgeEndpoints p hc i).1 x := by
      refine finite_component_right_reaches p _ (bridgeEndpoints p hc i).2 hm hv.1 ?_ x hxm ?_
      · intro y hy
        exact component_right_bound p _ y ((component_right_path p _).trans hy)
      · exact (CycleFootprint.load_path_symm _ (component_right_path p _)).trans hpath
    exact bridge_sequence_preserves_reach p _ (component_bridges_valid p hc)
      (component_bridges_separated p hc) (hxs _ hp)
  · let i : Fin k := ⟨j.val-1,by have := j.isLt; omega⟩
    have hij : i.succ=j := Fin.ext (by dsimp [i]; omega)
    rw [← hij] at hpath
    have hv := ordered_component_bridge_valid p hc i
    have hm := ((mem_source_packets p _).mp (bridge_endpoints_in_source_packets p hc i).2).1
    have hp : FiniteReach p (bridgeEndpoints p hc i).2 x := by
      refine finite_component_left_reaches p (bridgeEndpoints p hc i).1 _ hm hv.1 ?_ x hxm ?_
      · intro y hy
        exact component_left_bound p _ y ((component_left_path p _).trans hy)
      · exact (CycleFootprint.load_path_symm _ (component_left_path p _)).trans hpath
    exact (bridge_sequence_preserves_reach p _ (component_bridges_valid p hc)
      (component_bridges_separated p hc) (hxs _ hp)).trans (joined_component_chain_reverse p hc hk i)

/-- The new strong core consists exactly of the old source packets: no filling
vertex is absorbed into it by the bridges. -/
theorem joined_core_eq_source_packets (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    PrunedLift.core (joinedComponents p hc) (displacement (joinedComponents p hc).symm)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 = sourcePackets p := by
  ext x
  rw [PrunedLift.mem_core]
  constructor
  · intro hx
    exact joined_source_packets_predecessor_closed p hc hx.2 (bridge_endpoints_in_source_packets p hc ⟨0,hk⟩).1
  · intro hx
    have hm := ((mem_source_packets p x).mp hx).1
    have hm' : (joinedComponents p hc).symm x ≠ x := by
      apply (mem_support_inverse _ x).mp
      change x ∈ (bridgeSequence p (componentBridges p hc)).support
      rw [bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)]
      exact (mem_support_inverse p x).mpr hm
    exact ⟨joined_components_all_reached p hc hk x hm',source_vertex_reaches_joined_root p hc hk x hx⟩

#print axioms joined_core_eq_source_packets
end LRX.FiniteCuts
