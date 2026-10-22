import LRX.OutsideCycleSelection
import LRX.PaidPacketAssembly
import LRX.CircularOrderedRoute

/-! Build all services on one arc by separating its selected outside cycles
and retaining the rest in one packet service at a positive incident port. -/
namespace LRX.ZeroGap
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem arc_packet_service_family_load (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (forward : Bool) (start finish : Fin n)
    (cycles : List (State n)) (hcycles : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ outsideCycles p d 0)
    (hports : ∀ q ∈ cycles, (arcCoordinate forward start (cycleRoot q)).val ≤
      (arcCoordinate forward start finish).val)
    (r port : Fin n) (hr : PrunedLift.InCore p d 0 r) (hp : port=r ∨ port+1=r)
    (hport : (arcCoordinate forward start port).val ≤ (arcCoordinate forward start finish).val) :
    ∃ all : List (ExactService n),
      all.Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      (all.map (fun a => a.service.target)).prod=p ∧
      (∀ i, (all.map (fun a => a.displacement i)).sum=d i) ∧
      (∀ a ∈ all, (arcCoordinate forward start a.service.port).val ≤
        (arcCoordinate forward start finish).val) ∧
      ((all.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i : Fin n, |d i|)-2*(cycles.length : ℤ)-portLoad d port := by
  classical
  have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) h)
  let selected := (cycles.map (fun q => q⁻¹)).prod
  have hpart : CyclePart.IsPart selected p := outside_selected_part cycles hcycles hout
  have hkeep : PrunedLift.KeepsCore p d 0 selected.supportᶜ := outside_selected_keeps_core cycles hout
  have hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ) :=
    outside_selected_canonical hd hcover hmov cycles hcycles hout
  obtain ⟨ss,ht,hlen,hcan,hssports,hprices⟩ := outside_cycle_service_family hn hd hcover hmov cycles hout
  have hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_map.mp
    rw [ht]
    exact FiniteCuts.inverse_targets_disjoint cycles hcycles
  have htarget : (ss.map (fun a => a.service.target)).prod=selected := by rw [ht]
  have hS := PrunedLift.complement_invariant p selected.support (CyclePart.support_invariant selected p hpart)
  obtain ⟨a,ha,hat,had,har⟩ := PrunedLift.retained_incident_packet_service hn hd hshort hroot hcover
    selected.supportᶜ hS hkeep r port hr hp
  have hat' : a.service.target=CyclePart.remaining selected p hpart := hat
  obtain ⟨hall,heval,hdisp,hrot⟩ := paid_packet_assembly hpart hfinite ss hdis hcan htarget hprices
    a hat' had (portLoad d port) har
  refine ⟨a::ss,hall,heval,hdisp,?_,?_⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rwa [ha]
    · obtain ⟨q,hq,hqport⟩ := hssports b hb
      rw [hqport]
      exact hports q hq
  · rw [hlen] at hrot
    omega

theorem arc_packet_service_family (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (forward : Bool) (start finish : Fin n)
    (cycles : List (State n)) (hcycles : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ outsideCycles p d 0)
    (hports : ∀ q ∈ cycles, (arcCoordinate forward start (cycleRoot q)).val ≤
      (arcCoordinate forward start finish).val)
    (r port : Fin n) (hr : PrunedLift.InCore p d 0 r) (hp : port=r ∨ port+1=r)
    (hpos : 0 < portLoad d port)
    (hport : (arcCoordinate forward start port).val ≤ (arcCoordinate forward start finish).val) :
    ∃ all : List (ExactService n),
      all.Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      (all.map (fun a => a.service.target)).prod=p ∧
      (∀ i, (all.map (fun a => a.displacement i)).sum=d i) ∧
      (∀ a ∈ all, (arcCoordinate forward start a.service.port).val ≤
        (arcCoordinate forward start finish).val) ∧
      ((all.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i : Fin n, |d i|)-2*(cycles.length : ℤ)-2 := by
  obtain ⟨all,hdis,ht,hdisp,hrange,hrot⟩ := arc_packet_service_family_load hn hd hshort hroot hcover
    forward start finish cycles hcycles hout hports r port hr hp hport
  have hload := positive_port_load_ge_two hd port hpos
  exact ⟨all,hdis,ht,hdisp,hrange,by omega⟩

#print axioms arc_packet_service_family_load
#print axioms arc_packet_service_family
end LRX.ZeroGap
