import LRX.JoinedPacketCover
import LRX.PacketIncidentLoad

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem canonical_pruned_displacement (p : State n) (T : Finset (Fin n))
    (hT : ∀ i, p i ∈ T ↔ i ∈ T) :
    displacement (PrunedLift.permutation p T hT).symm=
      PrunedLift.displacement T (displacement p.symm) := by
  classical
  funext i
  by_cases hi : i ∈ T <;>
    simp [displacement,PrunedLift.permutation_symm_apply,PrunedLift.displacement,hi]

/-- Retain the core and any desired filling cycles, keeping the original finite
window and an arbitrary original root. -/
theorem finite_retained_packet_service (hn : 2 ≤ n) (p : State n) (r : Fin n)
    (hr : p.symm r ≠ r) (hcover : PrunedLift.PacketCover p (displacement p.symm) r)
    (T : Finset (Fin n)) (hT : ∀ i, p i ∈ T ↔ i ∈ T)
    (hkeep : PrunedLift.KeepsCore p (displacement p.symm) r T) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=PrunedLift.permutation p T hT ∧
      a.displacement=PrunedLift.displacement T (displacement p.symm) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |PrunedLift.displacement T (displacement p.symm) i|)-
          portLoad (displacement p.symm) r := by
  let q := PrunedLift.permutation p T hT
  have hrT : r ∈ T := hkeep r Relation.ReflTransGen.refl Relation.ReflTransGen.refl
  have hqr : q.symm r ≠ r := by simpa [q,PrunedLift.permutation_symm_apply,hrT] using hr
  have hreach : ∀ i, q.symm i ≠ i → FiniteReach q r i := by
    intro i hi
    have hiT : i ∈ T := by
      by_contra hh
      exact hi (by simp [q,PrunedLift.permutation_symm_apply,hh])
    have hpi : p.symm i ≠ i := by simpa [q,PrunedLift.permutation_symm_apply,hiT] using hi
    obtain ⟨b,j,hrb,hbr,he,hji⟩ := hcover i (displacement_ne_of_moved p.symm i hpi)
    have hbT := hkeep b hrb hbr
    have hjT := PrunedLift.same_cycle_mem p T hT hiT hji.symm
    have hpath := PrunedLift.retain_core_path p (displacement p.symm) r T hT hkeep
      r Relation.ReflTransGen.refl hrb hbr
    have hedge := PrunedLift.service_edge p (displacement p.symm) T hT hbT hjT he
    have hcycle := PrunedLift.same_cycle p T hT hjT hji
    have hall := (hpath.tail hedge).tail (Or.inl hcycle)
    rw [← canonical_pruned_displacement p T hT] at hall
    exact hall
  obtain ⟨a,ha,ht,hd,hrot⟩ := finite_reachable_exact_service hn q r hqr hreach
  rw [canonical_pruned_displacement p T hT] at hd hrot
  rw [PrunedLift.port_load_keeps_core hcover hr T hkeep r r
    ⟨Relation.ReflTransGen.refl,Relation.ReflTransGen.refl⟩ (Or.inl rfl)] at hrot
  exact ⟨a,ha,ht,hd,hrot⟩

#print axioms finite_retained_packet_service
end LRX.FiniteCuts
