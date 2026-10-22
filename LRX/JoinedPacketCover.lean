import LRX.JoinedFillings

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem joined_packet_cover (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    PrunedLift.PacketCover (joinedComponents p hc) (displacement (joinedComponents p hc).symm)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 := by
  let G := joinedComponents p hc
  let r := (bridgeEndpoints p hc ⟨0,hk⟩).1
  have hrT : r ∈ sourcePackets p := (bridge_endpoints_in_source_packets p hc ⟨0,hk⟩).1
  have hrm : G.symm r ≠ r := by
    apply (mem_support_inverse _ r).mp
    change r ∈ (bridgeSequence p (componentBridges p hc)).support
    rw [bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)]
    exact (mem_support_inverse p r).mpr ((mem_source_packets p r).mp hrT).1
  have hd : AffineLift.IsLift G 0 (displacement G.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift G.symm
  have hconn : ∀ b : CycleFootprint.Active G, CycleFootprint.LoadPath (displacement G.symm) r b.val := by
    intro b
    exact CycleFootprint.service_path_load_path hd (joined_components_all_reached p hc hk b.val b.property)
  obtain ⟨a,ha⟩ := CycleFootprint.connected_load_packet hd (displacement_short G.symm) ⟨r,hrm⟩ hconn
  have har := PrunedLift.packet_cover_reaches G _ a.val ha r (displacement_ne_of_moved G.symm r hrm)
  have hra := joined_components_all_reached p hc hk a.val a.property
  exact PrunedLift.packet_cover_reroot G _ a.val r ha har hra

theorem joined_packet_cover_at_source (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (r : Fin n) (hr : r ∈ sourcePackets p) :
    PrunedLift.PacketCover (joinedComponents p hc) (displacement (joinedComponents p hc).symm) r := by
  have hr' : PrunedLift.InCore (joinedComponents p hc) (displacement (joinedComponents p hc).symm)
      (bridgeEndpoints p hc ⟨0,hk⟩).1 r := by
    apply (PrunedLift.mem_core _ _ _ _).mp
    rw [joined_core_eq_source_packets p hc hk]
    exact hr
  exact PrunedLift.packet_cover_reroot _ _ _ r (joined_packet_cover p hc hk) hr'.1 hr'.2

#print axioms joined_packet_cover
#print axioms joined_packet_cover_at_source
end LRX.FiniteCuts
