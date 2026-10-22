import LRX.JoinedSourceCore

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

theorem source_packets_invariant (p : State n) (i : Fin n) :
    p i ∈ sourcePackets p ↔ i ∈ sourcePackets p := by
  have hc : (p⁻¹).SameCycle (p i) i := by
    simpa using (Equiv.Perm.SameCycle.refl (p⁻¹) (p i)).apply_right
  exact ⟨fun hi => source_packets_predecessor_closed p i (p i) (Or.inl hc.symm) hi,
    fun hi => source_packets_predecessor_closed p (p i) i (Or.inl hc) hi⟩

theorem joined_source_packets_invariant (p : State n) (hc : (componentRoots p).card=k+1)
    (hk : 0 < k) (i : Fin n) :
    joinedComponents p hc i ∈ sourcePackets p ↔ i ∈ sourcePackets p := by
  rw [← joined_core_eq_source_packets p hc hk]
  exact PrunedLift.core_invariant _ _ _ i

theorem joined_inverse_outside_packets (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin n) (hi : i ∉ sourcePackets p) : (joinedComponents p hc).symm i=p.symm i := by
  apply bridge_sequence_inverse_outside p _ i
  intro uv huv
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp huv
  have he := bridge_endpoints_in_source_packets p hc a
  exact ⟨fun h => hi (h ▸ he.1),fun h => hi (h ▸ he.2)⟩

theorem joined_forward_outside_packets (p : State n) (hc : (componentRoots p).card=k+1)
    (i : Fin n) (hi : i ∉ sourcePackets p) : joinedComponents p hc i=p i := by
  have hp : p i ∉ sourcePackets p := fun h => hi ((source_packets_invariant p i).mp h)
  have hh := joined_inverse_outside_packets p hc (p i) hp
  simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply] using (congrArg (joinedComponents p hc) hh).symm

/-- The entire filling permutation, not just its support or energy, is unchanged. -/
theorem joined_filling_permutation (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    PrunedLift.permutation (joinedComponents p hc) (sourcePackets p)ᶜ
      (PrunedLift.complement_invariant _ _ (joined_source_packets_invariant p hc hk)) =
    PrunedLift.permutation p (sourcePackets p)ᶜ
      (PrunedLift.complement_invariant _ _ (source_packets_invariant p)) := by
  classical
  ext i
  simp only [PrunedLift.permutation_apply]
  by_cases hi : i ∈ (sourcePackets p)ᶜ
  · simp only [hi,ite_true]
    exact congrArg Fin.val (joined_forward_outside_packets p hc i (Finset.mem_compl.mp hi))
  · simp only [hi,ite_false]

theorem joined_filling_displacement (p : State n) (hc : (componentRoots p).card=k+1) :
    PrunedLift.displacement (sourcePackets p)ᶜ (displacement (joinedComponents p hc).symm)=
    PrunedLift.displacement (sourcePackets p)ᶜ (displacement p.symm) := by
  classical
  funext i
  by_cases hi : i ∈ (sourcePackets p)ᶜ
  · simp only [PrunedLift.displacement,hi,ite_true,displacement,
      joined_inverse_outside_packets p hc i (Finset.mem_compl.mp hi)]
  · simp only [PrunedLift.displacement,hi,ite_false]

#print axioms joined_filling_permutation
#print axioms joined_filling_displacement
end LRX.FiniteCuts
