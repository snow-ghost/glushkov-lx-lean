import LRX.LoadedFootprint
import LRX.FootprintPathCover
import LRX.PacketExactService

/-! Positive load around the whole circle gives a concrete root packet and
an exact service, with no packet-existence hypothesis. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem overlap_of_loaded_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (a b : Active p) (hpath : Relation.ReflTransGen (LoadedStep d) a.val b.val) :
    FootprintGeometry.OverlapPath (activeFootprint p d) a b := by
  apply FootprintGeometry.overlap_path_of_covered_path (activeFootprint p d) (LoadedStep d)
    (fun _ _ => loaded_step_footprint hd hshort) a b _ _ hpath
  · exact support_subset p d a.val (BufferProgram.mem_own_orbit p a.val a.property)
  · exact support_subset p d b.val (BufferProgram.mem_own_orbit p b.val b.property)

theorem circle_path (x y : Fin n) : Relation.ReflTransGen Adjacent x y := by
  have h := segment_path (Finset.univ : Finset (Fin n)) (x : ℤ) (y : ℤ) (y : ℤ)
    ⟨by simp,by simp⟩ (fun _ _ _ => Finset.mem_univ _)
  have hp : InsidePath (Finset.univ : Finset (Fin n)) x y := by
    simpa only [Int.cast_natCast,Fin.cast_val_eq_self] using h
  clear h
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.tail he.2.2

theorem positive_load_path (d : Fin n → ℤ) (hpos : ∀ r, 0 < RotationWords.portLoad d r)
    (x y : Fin n) : Relation.ReflTransGen (LoadedStep d) x y := by
  have hp := circle_path x y
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v hp he ih =>
    apply ih.tail
    rcases he with hf | hb
    · exact Or.inl ⟨hf,hpos u⟩
    · exact Or.inr ⟨hb,hpos v⟩

theorem positive_load_packet {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (hpos : ∀ r, 0 < RotationWords.portLoad d r) :
    ∃ root : Active p, PrunedLift.PacketCover p d root.val := by
  obtain ⟨a,_,_⟩ := positive_load_footprint hd hshort 0 (hpos 0)
  exact exists_packet_cover hd hshort a
    (fun b => overlap_of_loaded_path hd hshort a b (positive_load_path d hpos a.val b.val))

/-- Actual service and its rotation count for a lift with no zero-load edge. -/
theorem positive_load_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (hpos : ∀ r, 0 < RotationWords.portLoad d r) :
    ∃ r : Fin n, ∃ a : RotationWords.ExactService n,
      a.service.port=r ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-RotationWords.portLoad d r := by
  obtain ⟨root,hcover⟩ := positive_load_packet hd hshort hpos
  have hroot : d root.val ≠ 0 := by
    intro hz
    have hr := AffineLift.lift_residue hd root.val
    simp only [hz,Int.cast_zero,add_zero] at hr
    exact root.property hr.symm
  exact ⟨root.val,RotationWords.packet_exact_service hn hd hshort root.val hroot hcover⟩

#print axioms positive_load_packet
#print axioms positive_load_exact_service
end LRX.CycleFootprint
