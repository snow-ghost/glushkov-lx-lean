import LRX.ServiceCertificate

/-! Insert an unserviced orbit at an already visited port. This increases the
serviced set, preserves every old visit, and adds exactly that orbit's price. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem extend_service {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (C : ServiceCertificate p d)
    (a : Fin n) (ha : (p⁻¹) a ≠ a) (hnew : a ∉ C.labels)
    (hvisit : Visits C.program initialLogical (PeriodicBuffer.contract (n : ℤ) (a : ℤ))) :
    ∃ D : ServiceCertificate p d, D.labels=C.labels ∪ orbitLabels p a := by
  obtain ⟨u, v, hprogram, hport⟩ := (visits_prefix _ _ _).mp hvisit
  let t := logicalRun u (initialLogical (n := n))
  let child := orbitChild p d a t.buffer
  have huses : ProgramUses C.labels u ∧ ProgramUses C.labels v := by
    apply (programUses_append _ _ _).mp
    rw [← hprogram]
    exact C.uses
  have hv : Valid u initialLogical ∧ Valid v t := by
    apply (valid_append _ _ _).mp
    rw [← hprogram]
    exact C.valid
  have hbuf : t.buffer ∈ C.labels := run_buffer_mem u initialLogical C.root_mem huses.1
  have hdis : Disjoint C.labels (orbitLabels p a) :=
    orbit_disjoint_of_not_mem p C.labels C.invariant a hnew
  have hout : t.buffer ∉ orbitLabels p a := Finset.disjoint_left.mp hdis hbuf
  have hcoords (i : Fin n) (hi : i ∈ orbitLabels p a) :
      t.coord i=PeriodicBuffer.contract (n : ℤ) (i : ℤ) := by
    have hn : i ∉ C.labels := fun h => Finset.disjoint_left.mp hdis h hi
    exact run_outside u initialLogical C.root_mem huses.1 i hn
  have hh : HeadReady t := by
    apply valid_head_ready u initialLogical _ hv.1
    simp [HeadReady, initialLogical, PeriodicBuffer.contract]
  have hentry : (t.coord a-t.head)%BufferMachine.slots n=0 := by
    rw [hcoords a (mem_own_orbit p a ha)]
    change Int.ModEq (BufferMachine.slots n) t.head (PeriodicBuffer.contract (n : ℤ) (a : ℤ)) at hport
    have h := hport.symm.sub_right t.head
    simpa only [sub_self, Int.zero_emod] using h.eq
  have hc := orbit_child_correct hd a ha t hout hcoords hh hentry
  have hframe : FrameEquivalent C.labels t (logicalRun child t) :=
    lifted_subtree_frame hd (orbitLabels p a) C.labels (orbitLabels_invariant p a)
      child t hc.2.2.1 hc.2.1 hdis
  have hframeEnd := (run_frame hframe hbuf v huses.2).1
  have hchildbuf : (logicalRun child t).buffer ∈ C.labels := by
    rw [hc.2.1]
    exact hbuf
  have hcoord (i : Fin n) : (logicalRun (u++child++v) initialLogical).coord i=
      (initialLogical (n := n)).coord i+
        if i ∈ C.labels ∪ orbitLabels p a then logicalDelta d i else 0 := by
    rw [logicalRun_append, logicalRun_append]
    change (logicalRun v (logicalRun child t)).coord i= _
    by_cases hi : i ∈ C.labels
    · rw [← hframeEnd.coord_eq i hi]
      have hold := C.coordinates i
      rw [hprogram, logicalRun_append] at hold
      simpa only [ite_eq_left hi, ite_eq_left (Finset.mem_union_left _ hi)] using hold
    · rw [run_outside v (logicalRun child t) hchildbuf huses.2 i hi, hc.2.2.1 i]
      rw [show t.coord i=(initialLogical (n := n)).coord i from
        run_outside u initialLogical C.root_mem huses.1 i hi]
      simp only [Finset.mem_union, hi, false_or]
  refine ⟨{
    labels := C.labels ∪ orbitLabels p a
    program := u++child++v
    invariant := by rw [Finset.image_union, C.invariant, orbitLabels_invariant]
    root_mem := Finset.mem_union_left _ C.root_mem
    uses := ?_
    valid := ?_
    coordinates := hcoord
    final_buffer := ?_
    rotation_price := ?_
    ports := ?_
  }, rfl⟩
  · rw [programUses_append, programUses_append]
    refine ⟨⟨programUses_mono Finset.subset_union_left huses.1, ?_⟩,
      programUses_mono Finset.subset_union_left huses.2⟩
    exact orbit_child_uses _ p d a t.buffer
      (Finset.mem_union_right _ (mem_own_orbit p a ha))
      (Finset.mem_union_left _ hbuf) Finset.subset_union_right
  · rw [valid_append, valid_append, logicalRun_append]
    exact ⟨⟨hv.1, hc.1⟩, valid_frame hframe hbuf v huses.2 hv.2⟩
  · rw [logicalRun_append, logicalRun_append]
    change p.symm (logicalRun v (logicalRun child t)).buffer=0
    rw [← hframeEnd.buffer_eq]
    have h := C.final_buffer
    rw [hprogram, logicalRun_append] at h
    exact h
  · rw [compile_append, rotations_append, compile_append, rotations_append,
      Finset.sum_union hdis]
    have hold := C.rotation_price
    rw [hprogram, compile_append, rotations_append] at hold
    have hprice := hc.2.2.2.2
    change rotations (compile child)=_ at hprice
    omega
  · intro i hi x hx
    rcases Finset.mem_union.mp hi with hi | hi
    · apply visits_insert u child v initialLogical hbuf huses.2 hframe
      rw [← hprogram]
      exact C.ports i hi x hx
    · apply (visits_append (u++child) v initialLogical _).mpr
      apply Or.inl
      apply (visits_append u child initialLogical _).mpr
      exact Or.inr (orbit_child_visits hd a ha t hcoords hentry i hi x hx)

#print axioms extend_service
end LRX.BufferProgram
