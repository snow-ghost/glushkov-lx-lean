import LRX.ArrowLoadPaths
import LRX.PositiveLoadPacket
import LRX.GeometricSourcePacket

/-! The physical positive-load components coincide with components of cycle
footprints, including when some circle edges have zero load. -/
namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem arrow_target_load_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i : Fin n) : LoadPath d i (p.symm i) := by
  have h := arrow_load_path d i ((i : ℤ)+d i) ⟨by simp,by simp⟩
  have he : (((i : ℤ)+d i : ℤ) : Fin n)=p.symm i := by simpa using AffineLift.lift_residue hd i
  simpa only [he] using h

theorem same_cycle_load_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {a i : Fin n} (hc : (p⁻¹).SameCycle a i) :
    LoadPath d a i := by
  obtain ⟨k,rfl⟩ := hc.exists_nat_pow_eq
  clear hc
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    have ht := arrow_target_load_path hd (((p⁻¹)^k) a)
    simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using ih.trans ht

theorem footprint_load_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a x : Fin n) (hx : x ∈ footprint p d a) :
    LoadPath d a x := by
  obtain ⟨i,hi,k,hlo,hhi⟩ := (mem_footprint p d a x).mp hx
  have hai := same_cycle_load_path hd ((BufferProgram.mem_orbitLabels p a i).mp hi).1
  have hix := arrow_load_path d i ((x : ℤ)+k*(n : ℤ)) ⟨hlo,hhi⟩
  rw [copy_cast] at hix
  exact hai.trans hix

theorem load_path_of_overlap {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {a b : Active p}
    (h : FootprintGeometry.Overlap (activeFootprint p d) a b) : LoadPath d a.val b.val := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hx
  exact (footprint_load_path hd a.val x ha).trans (load_path_symm d (footprint_load_path hd b.val x hb))

theorem load_path_of_overlap_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {a b : Active p}
    (h : FootprintGeometry.OverlapPath (activeFootprint p d) a b) : LoadPath d a.val b.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (load_path_of_overlap hd he)

theorem load_component_iff_overlap_component {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (a b : Active p) :
    LoadPath d a.val b.val ↔ FootprintGeometry.OverlapPath (activeFootprint p d) a b :=
  ⟨overlap_of_loaded_path hd hshort a b,load_path_of_overlap_path hd⟩

/-- A source packet for each physical load component, with direct coverage
of every moving cycle in that component. -/
theorem load_component_source_packet {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (initial : Active p) :
    ∃ root : Active p, LoadPath d initial.val root.val ∧
      (∀ a : Active p, PrunedLift.Reaches p d a.val root.val → PrunedLift.Reaches p d root.val a.val) ∧
      (∀ b : Active p, LoadPath d initial.val b.val → ∃ s x,
        PrunedLift.Reaches p d root.val s ∧ PrunedLift.Reaches p d s root.val ∧
        BufferProgram.ServiceEdge p d s x ∧ (p⁻¹).SameCycle x b.val) := by
  obtain ⟨root,hr,hs,hc⟩ := exists_source_packet hd initial
  exact ⟨root,load_path_of_overlap_path hd hr,hs,
    fun b hb => hc b (overlap_of_loaded_path hd hshort initial b hb)⟩

/-- A single physical load component suffices for the global service contract;
zero-load edges are allowed. -/
theorem connected_load_packet {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (initial : Active p)
    (hconn : ∀ b : Active p, LoadPath d initial.val b.val) :
    ∃ root : Active p, PrunedLift.PacketCover p d root.val :=
  exists_packet_cover hd hshort initial (fun b => overlap_of_loaded_path hd hshort initial b (hconn b))

#print axioms load_component_iff_overlap_component
#print axioms load_component_source_packet
#print axioms connected_load_packet
end LRX.CycleFootprint
