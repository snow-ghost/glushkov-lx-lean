import LRX.FiniteRetainedPacket
import LRX.PacketExactService

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem finite_retained_incident_packet_service (hn : 2 ≤ n) (p : State n) (r port : Fin n)
    (hr : p.symm r ≠ r) (hp : port=r ∨ port+1=r)
    (hcover : PrunedLift.PacketCover p (displacement p.symm) r)
    (T : Finset (Fin n)) (hT : ∀ i, p i ∈ T ↔ i ∈ T)
    (hkeep : PrunedLift.KeepsCore p (displacement p.symm) r T) :
    ∃ a : ExactService n, a.service.port=port ∧ a.service.target=PrunedLift.permutation p T hT ∧
      a.displacement=PrunedLift.displacement T (displacement p.symm) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |PrunedLift.displacement T (displacement p.symm) i|)-
          portLoad (displacement p.symm) port := by
  rcases hp with hp | hp
  · subst port
    exact finite_retained_packet_service hn p r hr hcover T hT hkeep
  · have hport : port=r-1 := by linear_combination hp
    let q := PrunedLift.permutation p T hT
    have hcoverq := PrunedLift.packet_cover_pruned p (displacement p.symm) r hcover T hT hkeep
    rw [← canonical_pruned_displacement p T hT] at hcoverq
    have hrT := hkeep r Relation.ReflTransGen.refl Relation.ReflTransGen.refl
    have hrq : q.symm r ≠ r := by simpa [q,PrunedLift.permutation_symm_apply,hrT] using hr
    have hd : AffineLift.IsLift q 0 (displacement q.symm) := by
      simpa only [Equiv.symm_symm] using canonical_lift q.symm
    obtain ⟨a,ha,ht,had,har⟩ := WordReflection.packet_exact_left_service hn hd
      (displacement_short q.symm) r (displacement_ne_of_moved q.symm r hrq) hcoverq
    rw [canonical_pruned_displacement p T hT] at had har
    rw [← hport,PrunedLift.port_load_keeps_core hcover hr T hkeep r port
      ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩ (Or.inr hp)] at har
    exact ⟨a,ha.trans hport.symm,ht,had,har⟩

#print axioms finite_retained_incident_packet_service
end LRX.FiniteCuts
