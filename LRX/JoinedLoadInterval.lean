import LRX.FiniteZeroPortBarrier

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_moved_iff (p : State n) (hc : (componentRoots p).card=k+1) (x : Fin n) :
    (joinedComponents p hc).symm x ≠ x ↔ p.symm x ≠ x := by
  rw [← mem_support_inverse,← mem_support_inverse]
  change x ∈ (bridgeSequence p (componentBridges p hc)).support ↔ x ∈ p.support
  rw [bridge_sequence_support p _ (component_bridges_valid p hc) (component_bridges_separated p hc)]

theorem joined_load_positive_between (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (port : Fin n)
    (hlo : (outerLeft p hc).val ≤ port.val) (hhi : port.val < (outerRight p hc).val) :
    0 < portLoad (displacement (joinedComponents p hc).symm) port := by
  obtain ⟨_,hL,hR,_,_⟩ := joined_outer_ports hn p hc hk
  have hm := (joined_moved_iff p hc (outerRight p hc)).mpr ((mem_source_packets p _).mp hR).1
  have hp := PrunedLift.packet_cover_reaches _ _ _
    (joined_packet_cover_at_source p hc hk (outerLeft p hc) hL) (outerRight p hc)
    (displacement_ne_of_moved _ _ hm)
  have hd : AffineLift.IsLift (joinedComponents p hc) 0 (displacement (joinedComponents p hc).symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift (joinedComponents p hc).symm
  exact load_path_crossed_port_positive _ (CycleFootprint.service_path_load_path hd hp) port hlo hhi

theorem joined_load_zero_outside (p : State n) (hc : (componentRoots p).card=k+1) (port : Fin n)
    (hout : port.val < (outerLeft p hc).val ∨ (outerRight p hc).val ≤ port.val) :
    portLoad (displacement (joinedComponents p hc).symm) port=0 := by
  let G := joinedComponents p hc
  have hhalf : halfLoad G.symm (port.val+1)=0 := by
    rw [forward_as_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    intro hi
    by_cases hfix : G.symm i=i
    · rw [hfix] at hi
      omega
    · have hb := moving_between_outer p hc i ((joined_moved_iff p hc i).mp hfix)
      have hm : G.symm (G.symm i) ≠ G.symm i := by
        intro hh
        exact hfix (G.symm.injective hh)
      have ht := moving_between_outer p hc (G.symm i) ((joined_moved_iff p hc _).mp hm)
      rcases hout with hout | hout <;> omega
  rw [port_load_eq_twice_half]
  change 2*(halfLoad G.symm (port.val+1) : ℤ)=0
  rw [hhalf]
  simp

theorem joined_load_positive_iff (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (port : Fin n) :
    0 < portLoad (displacement (joinedComponents p hc).symm) port ↔
      (outerLeft p hc).val ≤ port.val ∧ port.val < (outerRight p hc).val := by
  constructor
  · intro hp
    by_contra hh
    have hz := joined_load_zero_outside p hc port (by omega)
    omega
  · intro hp
    exact joined_load_positive_between hn p hc hk port hp.1 hp.2

#print axioms joined_load_positive_iff
end LRX.FiniteCuts
