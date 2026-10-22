import LRX.ConnectedLoadWord
import LRX.PacketExactService

namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem incident_packet_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (r port : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hp : port=r ∨ port+1=r) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d port+
        ((min (port-start).val (n-(port-start).val) : ℕ) : ℤ)+
        ((min (finish-port).val (n-(finish-port).val) : ℕ) : ℤ) := by
  have hs : ∃ a : ExactService n, a.service.port=port ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=(∑ i : Fin n, |d i|)-portLoad d port := by
    rcases hp with hp | hp
    · subst port
      exact packet_exact_service hn hd hshort r hroot hcover
    · have hport : port=r-1 := by linear_combination hp
      rw [hport]
      exact WordReflection.packet_exact_left_service hn hd hshort r hroot hcover
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := hs
  obtain ⟨w,he,hlen⟩ := reduced_route_from hn hd [a] (by simp) (by simp [ht])
    (by intro i; simp [hdisp]) start finish
  refine ⟨w,he,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,walkCost,ha] at hlen
  have hz := congrArg (fun k : ℕ => (k : ℤ)) hlen
  push_cast at hz
  omega

#print axioms incident_packet_word
end LRX.RotationWords
