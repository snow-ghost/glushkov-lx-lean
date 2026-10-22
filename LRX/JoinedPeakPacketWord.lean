import LRX.JoinedPeakPacketFamily

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_peak_packet_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r : Fin n) (hr : r ∈ sourcePackets p)
    (cycles : List (State n)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ fillingCycles p) (start finish : Fin n) :
    ∃ (ss : List (ExactService n)) (a : ExactService n) (w : List Letter),
      ss.map (fun s => s.service.target)=cycles.map (fun q => q⁻¹) ∧ a.service.port=r ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-
        portLoad (displacement (joinedComponents p hc).symm) r-
        (cycles.map (fun q => 2*(leftPeak q n : ℤ))).sum+
        (walkCost start finish ((a::ss).map ExactService.service) : ℤ) := by
  obtain ⟨ss,a,hst,ha,hcan,hpair,hprod,hrot⟩ := joined_peak_packet_family hn p hc hk r hr cycles hdis hout
  have hc' : ∀ b ∈ a::ss, ∀ i, b.displacement i=(b.service.target.symm i : ℤ)-(i : ℤ) := by
    intro b hb i
    exact congrFun (hcan b hb) i
  have hbelow : FiniteRankOrder.Below p (((a::ss).map (fun s => s.service.target)).prod) := by
    rw [hprod]
    exact (joined_components_prices p hc).1
  obtain ⟨w,he,_,_,_,hlen⟩ := arbitrary_finite_route_rank_transfer hn (a::ss) hpair hc' p hbelow start finish
  have hcost := route_rotations start finish ((a::ss).map ExactService.service)
  have hlen' : (w.length : ℤ)=(inversionNumber p : ℤ)+
      (BufferProgram.rotations (route start finish ((a::ss).map ExactService.service)) : ℤ) := by exact_mod_cast hlen
  have hcost' : (BufferProgram.rotations (route start finish ((a::ss).map ExactService.service)) : ℤ)=
      (((a::ss).map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)+
        (walkCost start finish ((a::ss).map ExactService.service) : ℤ) := by
    simpa only [List.map_map,Function.comp_def,Nat.cast_add] using congrArg (fun x : ℕ => (x : ℤ)) hcost
  exact ⟨ss,a,w,hst,ha,he,by omega⟩

#print axioms joined_peak_packet_word
end LRX.FiniteCuts
