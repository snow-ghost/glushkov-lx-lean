import LRX.GeometricPacket
import LRX.PacketPorts

/-! The source component obtained from footprints is also a source component
of the concrete service graph on moving vertices. -/
namespace LRX.CycleFootprint
variable {n : ℕ} [NeZero n]

theorem service_edge_passes (p : State n) (d : Fin n → ℤ) (a b : Active p)
    (he : BufferProgram.ServiceEdge p d a.val b.val) :
    FootprintGeometry.Passes (activeFootprint p d) (activeSupport p) a b := by
  refine ⟨b.val,?_,BufferProgram.mem_own_orbit p b.val b.property⟩
  rcases he with hc | ⟨_,ht⟩
  · exact support_subset p d a.val ((BufferProgram.mem_orbitLabels p a.val b.val).mpr ⟨hc,a.property⟩)
  · exact (mem_footprint p d a.val b.val).mpr
      ⟨a.val,BufferProgram.mem_own_orbit p a.val a.property,ht⟩

theorem service_path_passes (p : State n) (d : Fin n → ℤ) {x y : Fin n}
    (hx : p⁻¹ x ≠ x) (hy : p⁻¹ y ≠ y) (hpath : PrunedLift.Reaches p d x y) :
    FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail z y hp he ih =>
    have hz := PrunedLift.moving_reachable p d hx hp
    exact (ih hz).tail (service_edge_passes p d ⟨z,hz⟩ ⟨y,hy⟩ he)

/-- Every overlap component has a source packet in the actual service graph.
The direct coverage conclusion is restricted to that component. -/
theorem exists_source_packet {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (initial : Active p) :
    ∃ root : Active p,
      FootprintGeometry.OverlapPath (activeFootprint p d) initial root ∧
      (∀ a : Active p, PrunedLift.Reaches p d a.val root.val → PrunedLift.Reaches p d root.val a.val) ∧
      (∀ b : Active p, FootprintGeometry.OverlapPath (activeFootprint p d) initial b →
        ∃ s x, PrunedLift.Reaches p d root.val s ∧ PrunedLift.Reaches p d s root.val ∧
          BufferProgram.ServiceEdge p d s x ∧ (p⁻¹).SameCycle x b.val) := by
  obtain ⟨root,hr,hsource,hcover⟩ := exists_geometric_packet hd initial
  refine ⟨root,hr,?_,?_⟩
  · intro a ha
    exact pass_path_reaches p d (hsource a (service_path_passes p d a.property root.property ha))
  · intro b hb
    obtain ⟨a,hra,har,he⟩ := hcover b hb
    obtain ⟨s,x,has,hsx,hxb⟩ := pass_service_witness p d a b he
    have hrs : PrunedLift.Reaches p d root.val s := (pass_path_reaches p d hra).tail (Or.inl has)
    have hsa : PrunedLift.Reaches p d s a.val := Relation.ReflTransGen.single (Or.inl has.symm)
    exact ⟨s,x,hrs,hsa.trans (pass_path_reaches p d har),hsx,hxb⟩

#print axioms service_path_passes
#print axioms exists_source_packet
end LRX.CycleFootprint
