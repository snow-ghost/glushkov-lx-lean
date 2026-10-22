import LRX.FiniteGlobalPeak
import LRX.JoinedCoreEnergy

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

noncomputable def sourceTarget (p : State n) : State n :=
  PrunedLift.permutation p (sourcePackets p) (source_packets_invariant p)
noncomputable def sourceHalfPeak (p : State n) : ℕ := leftPeak (sourceTarget p).symm n

theorem pruned_port_load_le (T : Finset (Fin n)) (d : Fin n → ℤ) (port : Fin n) :
    portLoad (PrunedLift.displacement T d) port ≤ portLoad d port := by
  classical
  rw [port_load_original,port_load_original]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ T
  · simp only [PrunedLift.displacement,hi,ite_true]
    exact le_rfl
  · simp only [PrunedLift.displacement,hi,ite_false,add_zero,PeriodicBuffer.edgePassages,sub_self,abs_zero]
    exact abs_nonneg _

theorem joined_source_peak_port (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    ∃ r ∈ sourcePackets p, 2*(sourceHalfPeak p : ℤ) ≤
      portLoad (displacement (joinedComponents p hc).symm) r := by
  let u := (bridgeEndpoints p hc ⟨0,hk⟩).1
  have hu := (bridge_endpoints_in_source_packets p hc ⟨0,hk⟩).1
  change u ∈ sourcePackets p at hu
  have hum := ((mem_source_packets p u).mp hu).1
  have hum' : (sourceTarget p).symm u ≠ u := by
    simpa only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hu] using hum
  have hpos := moved_global_peak_positive (sourceTarget p).symm u hum'
  obtain ⟨r,hrm,_,hpeak⟩ := left_peak_port (sourceTarget p).symm n le_rfl hpos
  have hr : r ∈ sourcePackets p := by
    by_contra hh
    exact hrm (by simp [sourceTarget,PrunedLift.permutation_symm_apply,hh])
  have he : displacement (sourceTarget p).symm=PrunedLift.displacement (sourcePackets p) (displacement p.symm) := by
    funext i
    by_cases hi : i ∈ sourcePackets p <;>
      simp [sourceTarget,displacement,PrunedLift.displacement,PrunedLift.permutation_symm_apply,hi]
  have hb := pruned_port_load_le (sourcePackets p) (displacement p.symm) r
  rw [← he,port_load_eq_twice_half,hpeak] at hb
  have hmono : portLoad (displacement p.symm) r ≤ portLoad (displacement (joinedComponents p hc).symm) r := by
    rw [port_load_eq_twice_half,port_load_eq_twice_half]
    have hm := bridge_sequence_half_load p _ (component_bridges_valid p hc) (component_bridges_separated p hc) (r.val+1)
    exact_mod_cast Nat.mul_le_mul_left 2 hm
  exact ⟨r,hr,hb.trans hmono⟩

#print axioms joined_source_peak_port
end LRX.FiniteCuts
