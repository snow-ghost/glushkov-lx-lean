import LRX.PortEndpoints

/-! Closed reachable services retain their exact integer endpoint contract
at the physical port, for every integer representative of the cursor. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exists_exact_closed_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (r : Fin n) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p 0 r)
        (localDisplacement d r)) 0 i) :
    ∃ service : ClosedService n,
      service.port=r ∧ service.target=p ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d r ∧
      (∀ z i, (LiftedModel.run service.word (LiftedModel.atPort r z)).position i=
        (i : ℤ)+d i) := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have hlift := recentered_lift 0 r hd0
  have hne : localDisplacement d r 0 ≠ 0 := by
    simpa only [local_displacement_zero] using hroot
  have hlocalroot : (localTarget p 0 r)⁻¹ 0 ≠ 0 := by
    intro h
    exact hne (BufferProgram.fixed_short_displacement hlift 0 (hshort _) h)
  obtain ⟨w, heval, hcursor, hend, hx, hprice⟩ :=
    BufferProgram.reachable_service_price hn hlift hlocalroot hreach
  have hclosed : (w.map LiftedModel.increment).sum=0 := by
    simpa only [LiftedModel.cursor_run, LiftedModel.initial, zero_add] using hcursor
  rw [inversion_count_recentered 0 r hd0] at hx hprice
  rw [local_displacement_mass] at hprice
  refine ⟨⟨r, w, p, heval.trans (local_target_zero p r), hclosed⟩, rfl, rfl, hx, hprice, ?_⟩
  intro z
  exact LiftedModel.port_run_positions w r z d hend

#print axioms exists_exact_closed_service
end LRX.RotationWords
