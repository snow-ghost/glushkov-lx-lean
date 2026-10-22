import LRX.RootChildrenAssembly
import LRX.PrunedPacketService

/-! Both full-target boundary routes for a multi-cycle retained root packet. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_root_children_left_route (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hpart : CyclePart.IsPart selected p) (hcore : PrunedLift.KeepsCore p d 0 selected.supportᶜ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (ht : (services.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hprice : (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-discount)
    (finish : Fin n) (hports : ∀ a ∈ services, a.service.port.val ≤ finish.val) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-discount+(finish.val : ℤ) := by
  obtain ⟨a,ha,hat,had,har⟩ := CyclePart.packet_part_root_service hn hd hshort hroot hcover hpart hcore hfinite
  exact assemble_periodic_left_word hn hpart hfinite services hdis hc ht discount hprice finish hports a ha hat had har


theorem packet_root_children_right_route (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hpart : CyclePart.IsPart selected p)
    (hcore : PrunedLift.KeepsCore p d r selected.supportᶜ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i ∈ selected.support, i.val < r.val)
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (ht : (services.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hprice : (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-discount)
    (start finish : Fin n) (hs : start.val ≤ (r-1 : Fin n).val) (hf : finish.val ≤ (r-1 : Fin n).val)
    (hports : ∀ a ∈ services, start.val ≤ a.service.port.val ∧ a.service.port.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-discount+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  obtain ⟨a,ha,hat,had,har⟩ := CyclePart.packet_part_right_root_service hn hd hshort r hr hroot hcover hpart hcore hfinite hleft
  exact assemble_periodic_right_word hn hd r hpart hfinite services hdis hc ht discount hprice start finish hs hf hports a ha hat had har

#print axioms packet_root_children_left_route
#print axioms packet_root_children_right_route
end LRX.RotationWords
