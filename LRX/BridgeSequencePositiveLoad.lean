import LRX.JoinedIncidentWord

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem bridge_sequence_positive_load (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs)
    (uv : Fin n × Fin n) (huv : uv ∈ xs) (e : ℕ) (he : uv.1.val < e ∧ e ≤ uv.2.val) :
    1 ≤ halfLoad (bridgeSequence p xs).symm e := by
  induction xs generalizing p with
  | nil => simp at huv
  | cons xy xs ih =>
    have hvt := valid_bridge_tail p xy xs hv hs
    have hst := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp huv with hh | hh
    · subst uv
      have hvalid := hv xy (by simp)
      have hload := component_bridge_half_load p xy.1 xy.2 hvalid.1
        (le_of_lt hvalid.2.1) (le_of_lt hvalid.2.2.1) e
      rw [if_pos he] at hload
      have hmono := bridge_sequence_half_load (componentBridge p xy.1 xy.2) xs hvt hst e
      change 1 ≤ halfLoad (bridgeSequence (componentBridge p xy.1 xy.2) xs).symm e
      omega
    · exact ih _ hvt hst hh

theorem joined_bridge_port_load (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin k) (port : Fin n)
    (hlo : (bridgeEndpoints p hc i).1.val ≤ port.val)
    (hhi : port.val < (bridgeEndpoints p hc i).2.val) :
    2 ≤ portLoad (displacement (joinedComponents p hc).symm) port := by
  rw [port_load_eq_twice_half]
  have hh := bridge_sequence_positive_load p _ (component_bridges_valid p hc)
    (component_bridges_separated p hc) (bridgeEndpoints p hc i)
    (List.mem_ofFn.mpr ⟨i,rfl⟩) (port.val+1) ⟨by omega,by omega⟩
  change 1 ≤ halfLoad (joinedComponents p hc).symm (port.val+1) at hh
  exact_mod_cast (show 2 ≤ 2*halfLoad (joinedComponents p hc).symm (port.val+1) by omega)

#print axioms joined_bridge_port_load
end LRX.FiniteCuts
