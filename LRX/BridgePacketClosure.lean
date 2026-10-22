import LRX.JoinedComponentWord

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- No new service edge enters a predecessor-closed set when inverse arrows
outside it and the moving support are unchanged. -/
theorem service_edge_outside_preserved (p q : State n) (T : Finset (Fin n))
    (hclosed : ∀ i j, BufferProgram.ServiceEdge p (displacement p.symm) i j → j ∈ T → i ∈ T)
    (hag : ∀ i, i ∉ T → q.symm i=p.symm i)
    (hm : ∀ i, q.symm i ≠ i → p.symm i ≠ i)
    {i j : Fin n} (hi : i ∉ T)
    (he : BufferProgram.ServiceEdge q (displacement q.symm) i j) : j ∉ T := by
  have hstep (x : Fin n) (hx : x ∉ T) : q.symm x ∉ T := by
    rw [hag x hx]
    intro hy
    exact hx (hclosed x (p.symm x) (Or.inl ((Equiv.Perm.SameCycle.refl (p⁻¹) x).apply_right)) hy)
  rcases he with hcycle | ⟨hj,ht⟩
  · obtain ⟨t,ht⟩ := hcycle.exists_nat_pow_eq
    have hh : ∀ t : ℕ, (((q⁻¹)^t) i) ∉ T := by
      intro t
      induction t with
      | zero => simpa using hi
      | succ t ih =>
        rw [pow_succ',Equiv.Perm.mul_apply]
        exact hstep _ ih
    simpa only [ht] using hh t
  · have hedge : BufferProgram.ServiceEdge p (displacement p.symm) i j := by
      right
      refine ⟨hm j hj,?_⟩
      simpa only [displacement,hag i hi] using ht
    exact fun hjT => hi (hclosed i j hedge hjT)

theorem bridge_sequence_predecessor_closed (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs)
    (T : Finset (Fin n)) (hend : ∀ uv ∈ xs, uv.1 ∈ T ∧ uv.2 ∈ T)
    (hclosed : ∀ i j, BufferProgram.ServiceEdge p (displacement p.symm) i j → j ∈ T → i ∈ T)
    {i j : Fin n} (hr : FiniteReach (bridgeSequence p xs) i j) (hj : j ∈ T) : i ∈ T := by
  have hag : ∀ x, x ∉ T → (bridgeSequence p xs).symm x=p.symm x := by
    intro x hx
    apply bridge_sequence_inverse_outside p xs x
    intro uv huv
    exact ⟨fun he => hx (he ▸ (hend uv huv).1),fun he => hx (he ▸ (hend uv huv).2)⟩
  have hm : ∀ x, (bridgeSequence p xs).symm x ≠ x → p.symm x ≠ x := by
    intro x hx
    apply (mem_support_inverse p x).mp
    rw [← bridge_sequence_support p xs hv hs]
    exact (mem_support_inverse _ x).mpr hx
  induction hr with
  | refl => exact hj
  | tail hp he ih =>
    apply ih
    by_contra hx
    exact service_edge_outside_preserved p _ T hclosed hag hm hx he hj

#print axioms service_edge_outside_preserved
#print axioms bridge_sequence_predecessor_closed
end LRX.FiniteCuts
