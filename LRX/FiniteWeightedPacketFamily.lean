import LRX.FiniteRetainedIncidentPacket
import LRX.GlobalPeakServiceFamily

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem finite_weighted_packet_family (hn : 2 ≤ n) (p selected : State n)
    (r port : Fin n) (hr : p.symm r ≠ r) (hport : port=r ∨ port+1=r)
    (hcover : PrunedLift.PacketCover p (displacement p.symm) r)
    (hpart : CyclePart.IsPart selected p)
    (hkeep : PrunedLift.KeepsCore p (displacement p.symm) r selected.supportᶜ)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (ht : (ss.map (fun a => a.service.target)).prod=selected)
    (saving : ExactService n → ℤ)
    (hp : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ) ≤
      (∑ i, |a.displacement i|)-saving a) :
    ∃ a : ExactService n, a.service.port=port ∧ CanonicalFamily (a::ss) ∧
      (a::ss).Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      ((a::ss).map (fun a => a.service.target)).prod=p ∧
      (((a::ss).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i, |displacement p.symm i|)-portLoad (displacement p.symm) port-(ss.map saving).sum := by
  have hT := PrunedLift.complement_invariant p selected.support (CyclePart.support_invariant selected p hpart)
  obtain ⟨a,ha,hat,had,har⟩ := finite_retained_incident_packet_service hn p r port hr hport hcover selected.supportᶜ hT hkeep
  have hfinite : ∀ i ∈ selected.support, displacement p.symm i=(selected.symm i : ℤ)-(i : ℤ) := by
    intro i hi
    rw [displacement,CyclePart.inverse_on_support selected p hpart i hi]
  have hat' : a.service.target=CyclePart.remaining selected p hpart := hat
  obtain ⟨hpair,hprod,_,hprice⟩ := weighted_packet_assembly hpart hfinite ss hdis hcan ht saving hp
    a hat' had (portLoad (displacement p.symm) port) har
  refine ⟨a,ha,?_,hpair,hprod,hprice⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · rw [had,hat,← canonical_pruned_displacement p selected.supportᶜ hT]
    rfl
  · exact hcan b hb

#print axioms finite_weighted_packet_family
end LRX.FiniteCuts
