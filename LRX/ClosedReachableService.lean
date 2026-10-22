import LRX.PortRoute

/-! Closed route tasks are supplied by the proved lifted service construction.
Their contracts do not require a separately assumed word or execution witness. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_target_zero (p : State n) (r : Fin n) :
    localTarget p 0 r=(rotation r)⁻¹*p*rotation r := by
  change (rotation r)⁻¹*p*(rotation (0-r))⁻¹= _
  rw [rotation_sub]
  simp [rotation]

def idleService (r : Fin n) : ClosedService n where
  port := r
  word := []
  target := 1
  correct := by simp
  closed := rfl

/-- Every balanced reachable cluster supplies a real closed service at its
chosen port, with the exact original exchange price and load discount. -/
theorem exists_closed_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
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
        (∑ i : Fin n, |d i|)-portLoad d r := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have hlift := recentered_lift 0 r hd0
  have hne : localDisplacement d r 0 ≠ 0 := by
    simpa only [local_displacement_zero] using hroot
  have hlocalroot : (localTarget p 0 r)⁻¹ 0 ≠ 0 := by
    intro h
    exact hne (BufferProgram.fixed_short_displacement hlift 0 (hshort _) h)
  obtain ⟨w, heval, hcursor, _, hx, hprice⟩ :=
    BufferProgram.reachable_service_price hn hlift hlocalroot hreach
  have hclosed : (w.map LiftedModel.increment).sum=0 := by
    simpa only [LiftedModel.cursor_run, LiftedModel.initial, zero_add] using hcursor
  rw [inversion_count_recentered 0 r hd0] at hx hprice
  rw [local_displacement_mass] at hprice
  refine ⟨⟨r, w, p, heval.trans (local_target_zero p r), hclosed⟩, rfl, rfl, hx, ?_⟩
  exact hprice

#print axioms exists_closed_service
end LRX.RotationWords
