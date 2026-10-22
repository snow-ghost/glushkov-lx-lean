import LRX.JoinedPeakPacketWord
import LRX.CircularRankTransfer

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- Given the selected peak services lying on this arc, the original map has
an actual word with the full selected peak discount and only the arc approach
cost. Selecting the two families and the root peak ports is a separate step. -/
theorem joined_peak_arc_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r port : Fin n) (hr : r ∈ sourcePackets p) (hincident : port=r ∨ port+1=r)
    (cycles : List (State n)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hout : ∀ q ∈ cycles, q ∈ fillingCycles p)
    (ss : List (ExactService n))
    (hst : ss.map (fun s => s.service.target)=cycles.map (fun q => q⁻¹))
    (hcan : CanonicalFamily ss)
    (hprice : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ))
    (forward : Bool) (start finish : Fin n)
    (hrootport : (arcCoordinate forward start port).val ≤ (arcCoordinate forward start finish).val)
    (hports : ∀ a ∈ ss, (arcCoordinate forward start a.service.port).val ≤
      (arcCoordinate forward start finish).val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-
        portLoad (displacement (joinedComponents p hc).symm) port-
        (cycles.map (fun q => 2*(leftPeak q n : ℤ))).sum+
        ((arcCoordinate forward start finish).val : ℤ) := by
  obtain ⟨a,ha,hcanonical,hpair,hprod,hrot⟩ :=
    joined_selected_peak_family hn p hc hk r port hr hincident cycles hdis hout ss hst hcan hprice
  have hbelow : FiniteRankOrder.Below p (((a::ss).map (fun s => s.service.target)).prod) := by
    rw [hprod]
    exact (joined_components_prices p hc).1
  have hrange : ∀ b ∈ a::ss, (arcCoordinate forward start b.service.port).val ≤
      (arcCoordinate forward start finish).val := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simpa only [ha] using hrootport
    · exact hports b hb
  obtain ⟨w,he,hl⟩ := circular_rank_transfer_route hn p forward start finish (a::ss) hpair hcanonical hbelow hrange
  have hl' : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
      (((a::ss).map (fun s => BufferProgram.rotations s.service.word)).sum : ℤ)+
      ((arcCoordinate forward start finish).val : ℤ) := by exact_mod_cast hl
  exact ⟨w,he,by omega⟩

#print axioms joined_peak_arc_word
end LRX.FiniteCuts
