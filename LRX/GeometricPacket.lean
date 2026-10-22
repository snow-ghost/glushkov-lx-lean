import LRX.ConnectedCycleFootprint
import LRX.FootprintPacket
import LRX.PacketCoverage

/-! Source packets for the footprints of actual lifted permutation cycles. -/
namespace LRX.CycleFootprint
variable {n : ℕ} [NeZero n]

abbrev Active (p : State n) := {a : Fin n // p⁻¹ a ≠ a}

noncomputable def activeFootprint (p : State n) (d : Fin n → ℤ) : Active p → Finset (Fin n) :=
  fun a => footprint p d a.val

noncomputable def activeSupport (p : State n) : Active p → Finset (Fin n) :=
  fun a => BufferProgram.orbitLabels p a.val

theorem exists_geometric_packet {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (initial : Active p) :
    ∃ root : Active p, FootprintGeometry.OverlapPath (activeFootprint p d) initial root ∧
      (∀ a, FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) a root →
        FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) root a) ∧
      (∀ b, FootprintGeometry.OverlapPath (activeFootprint p d) initial b → ∃ a,
        FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) root a ∧
        FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) a root ∧
        FootprintGeometry.Passes (activeFootprint p d) (activeSupport p) a b) := by
  classical
  exact FootprintGeometry.exists_packet_from_geometry (activeFootprint p d) (activeSupport p)
    Adjacent (fun a => support_subset p d a.val)
    (fun a => ⟨a.val,BufferProgram.mem_own_orbit p a.val a.property⟩)
    (fun a => connected hd a.val a.property) (fun a => boundary_in_support hd a.val) initial

theorem pass_service_witness (p : State n) (d : Fin n → ℤ) (a b : Active p)
    (h : FootprintGeometry.Passes (activeFootprint p d) (activeSupport p) a b) :
    ∃ i x, (p⁻¹).SameCycle a.val i ∧ BufferProgram.ServiceEdge p d i x ∧
      (p⁻¹).SameCycle x b.val := by
  obtain ⟨x,hx,hxb⟩ := h
  obtain ⟨i,hi,ht⟩ := (mem_footprint p d a.val x).mp hx
  have hai := ((BufferProgram.mem_orbitLabels p a.val i).mp hi).1
  have hbx := ((BufferProgram.mem_orbitLabels p b.val x).mp hxb).1
  have hmx : p⁻¹ x ≠ x := fun hf => b.property (hbx.apply_eq_self_iff.mpr hf)
  exact ⟨i,x,hai,Or.inr ⟨hmx,ht⟩,hbx.symm⟩

theorem pass_reaches (p : State n) (d : Fin n → ℤ) (a b : Active p)
    (h : FootprintGeometry.Passes (activeFootprint p d) (activeSupport p) a b) :
    PrunedLift.Reaches p d a.val b.val := by
  obtain ⟨i,x,hai,he,hxb⟩ := pass_service_witness p d a b h
  have hfirst : PrunedLift.Reaches p d a.val i := Relation.ReflTransGen.single (Or.inl hai)
  exact (hfirst.tail he).tail (Or.inl hxb)

theorem pass_path_reaches (p : State n) (d : Fin n → ℤ) {a b : Active p}
    (h : FootprintGeometry.PassPath (activeFootprint p d) (activeSupport p) a b) :
    PrunedLift.Reaches p d a.val b.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (pass_reaches p d _ _ he)

/-- Connected cycle footprints give a root satisfying the concrete service contract. -/
theorem exists_packet_cover {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (initial : Active p)
    (hconnected : ∀ b : Active p, FootprintGeometry.OverlapPath (activeFootprint p d) initial b) :
    ∃ root : Active p, PrunedLift.PacketCover p d root.val := by
  obtain ⟨root,_,_,hcover⟩ := exists_geometric_packet hd initial
  refine ⟨root,?_⟩
  intro i hi
  have hmi : p⁻¹ i ≠ i := fun hf => hi (BufferProgram.fixed_short_displacement hd i (hshort i) hf)
  let b : Active p := ⟨i,hmi⟩
  obtain ⟨a,hra,har,he⟩ := hcover b (hconnected b)
  obtain ⟨s,x,has,hsx,hxi⟩ := pass_service_witness p d a b he
  have hrs : PrunedLift.Reaches p d root.val s := (pass_path_reaches p d hra).tail (Or.inl has)
  have hsa : PrunedLift.Reaches p d s a.val := Relation.ReflTransGen.single (Or.inl has.symm)
  exact ⟨s,x,hrs,hsa.trans (pass_path_reaches p d har),hsx,hxi⟩

#print axioms exists_geometric_packet
#print axioms exists_packet_cover
end LRX.CycleFootprint
