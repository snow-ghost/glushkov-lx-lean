import LRX.LoadComponentSet
import LRX.PacketExactService

/-! A literal exact service for each nontrivial physical load component after
any zero-load cut. Packet existence and component balance are derived. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem component_packet_cover {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (initial : Active p) :
    ∃ root : Active p, root.val ∈ component d initial.val ∧
      PrunedLift.PacketCover
        (PrunedLift.permutation p (component d initial.val) (component_invariant hd initial.val))
        (PrunedLift.displacement (component d initial.val) d) root.val := by
  classical
  let S := component d initial.val
  have hS := component_invariant hd initial.val
  obtain ⟨root,hr,_,hcover⟩ := load_component_source_packet hd hshort initial
  have hrS : root.val ∈ S := (mem_component d initial.val root.val).mpr hr
  have hcore := component_keeps_core hd initial.val root.val hrS
  refine ⟨root,hrS,?_⟩
  intro i hi
  change PrunedLift.displacement S d i ≠ 0 at hi
  have hiS : i ∈ S := by by_contra h; exact hi (by simp only [PrunedLift.displacement,ite_eq_right h])
  have hdi : d i ≠ 0 := by simpa only [PrunedLift.displacement,ite_eq_left hiS] using hi
  have hmi : p⁻¹ i ≠ i := fun hf => hdi (BufferProgram.fixed_short_displacement hd i (hshort i) hf)
  obtain ⟨s,x,hrs,hsr,he,hxi⟩ := hcover ⟨i,hmi⟩ ((mem_component d initial.val i).mp hiS)
  have hsS : s ∈ S := hcore s hrs hsr
  have hxS := PrunedLift.same_cycle_mem p S hS hiS hxi.symm
  refine ⟨s,x,?_,?_,PrunedLift.service_edge p d S hS hsS hxS he,
    PrunedLift.same_cycle p S hS hxS hxi⟩
  · exact PrunedLift.retain_core_path p d root.val S hS hcore root.val Relation.ReflTransGen.refl hrs hsr
  · exact PrunedLift.retain_core_path p d root.val S hS hcore s hrs hsr Relation.ReflTransGen.refl

theorem component_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (cut : Fin n) (hz : RotationWords.portLoad d cut=0) (initial : Active p) :
    ∃ r : Fin n, ∃ a : RotationWords.ExactService n,
      r ∈ component d initial.val ∧ a.service.port=r ∧
      a.service.target=PrunedLift.permutation p (component d initial.val) (component_invariant hd initial.val) ∧
      a.displacement=PrunedLift.displacement (component d initial.val) d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement (component d initial.val) d i|)-
          RotationWords.portLoad (PrunedLift.displacement (component d initial.val) d) r := by
  obtain ⟨root,hr,hcover⟩ := component_packet_cover hd hshort initial
  have hroot : d root.val ≠ 0 := by
    intro hz
    have he := AffineLift.lift_residue hd root.val
    simp only [hz,Int.cast_zero,add_zero] at he
    exact root.property he.symm
  have hr' : PrunedLift.displacement (component d initial.val) d root.val ≠ 0 := by
    simpa [PrunedLift.displacement,hr] using hroot
  have hlocal := PrunedLift.is_lift hd (component d initial.val) (component_invariant hd initial.val)
    (component_balanced hd cut hz initial.val)
  obtain ⟨a,ha,ht,hd',hp⟩ := RotationWords.packet_exact_service hn hlocal
    (PrunedLift.short hshort _) root.val hr' hcover
  exact ⟨root.val,a,hr,ha,ht,hd',hp⟩

#print axioms component_packet_cover
#print axioms component_exact_service
end LRX.CycleFootprint
