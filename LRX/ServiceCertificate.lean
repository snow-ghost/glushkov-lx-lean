import LRX.ItineraryPorts

/-! A finite service certificate records actual commands, exact delivered
coordinates, rotation price, and every port visited by serviced arrows. It is
intended to be enlarged by insertion until all reachable cycles are covered. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

structure ServiceCertificate (p : State n) (d : Fin n → ℤ) where
  labels : Finset (Fin n)
  program : List (Command n)
  invariant : labels.image p.symm=labels
  root_mem : (0 : Fin n) ∈ labels
  uses : ProgramUses labels program
  valid : Valid program initialLogical
  coordinates : ∀ i, (logicalRun program initialLogical).coord i=
    (initialLogical (n := n)).coord i+if i ∈ labels then logicalDelta d i else 0
  final_buffer : p.symm (logicalRun program initialLogical).buffer=0
  rotation_price : rotations (compile program)=∑ i ∈ labels, (logicalDelta d i).natAbs
  ports : ∀ i ∈ labels, ∀ v : ℤ,
    min (i : ℤ) ((i : ℤ)+d i) ≤ v ∧ v ≤ max (i : ℤ) ((i : ℤ)+d i) →
    Visits program initialLogical (PeriodicBuffer.contract (n : ℤ) v)

/-- The root cycle supplies a real seed certificate, even when its individual
winding is nonzero and other cycles have not yet been serviced. -/
theorem root_service_certificate {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : (p⁻¹) 0 ≠ 0) :
    Nonempty (ServiceCertificate p d) := by
  obtain ⟨rest, he, hnd, hset, hfollow⟩ := exists_orbit_itinerary p 0 hroot
  have hm (i : Fin n) : i ∈ (0 : Fin n)::rest ↔ i ∈ orbitLabels p 0 := by
    rw [← hset, List.mem_toFinset]
  have hh : HeadReady (initialLogical (n := n)) := by
    simp [HeadReady, initialLogical, PeriodicBuffer.contract]
  refine ⟨{
    labels := orbitLabels p 0
    program := itinerary (logicalDelta d) ((0 : Fin n)::rest)
    invariant := orbitLabels_invariant p 0
    root_mem := mem_own_orbit p 0 hroot
    uses := itinerary_uses _ _ _ (fun i hi => (hm i).mp hi)
    valid := itinerary_valid (initialLogical (n := n)).coord (logicalDelta d) 0 rest
      initialLogical hnd rfl (fun _ _ => rfl) hh (follows_compatible hd _ hfollow)
    coordinates := ?_
    final_buffer := ?_
    rotation_price := ?_
    ports := ?_
  }⟩
  · intro i
    simpa only [hm] using itinerary_coordinates (logicalDelta d) 0 rest initialLogical hnd rfl i
  · rw [itinerary_buffer (logicalDelta d) 0 rest (initialLogical (n := n)) rfl]
    exact orbit_last_target p 0 rest he
  · rw [itinerary_rotation_price, ← List.sum_toFinset _ hnd, hset]
  · intro i hi v hv
    exact lifted_itinerary_visits hd 0 rest initialLogical hnd rfl (fun _ _ => rfl)
      hh hfollow i ((hm i).mpr hi) v hv

#print axioms root_service_certificate
end LRX.BufferProgram
