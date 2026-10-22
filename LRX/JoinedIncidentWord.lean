import LRX.JoinedTwoArcBound

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_incident_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (r port : Fin n)
    (hr : r ∈ sourcePackets p) (hp : port=r ∨ port+1=r) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-portLoad (displacement (joinedComponents p hc).symm) port+
        (min (port-start).val (n-(port-start).val)+min (finish-port).val (n-(finish-port).val) : ℕ) := by
  obtain ⟨a,ha,hcan,hpair,hprod,hrot⟩ := joined_selected_peak_family hn p hc hk r port hr hp []
    (by simp) (by simp) [] rfl (by simp [CanonicalFamily]) (by simp)
  have hc' : ∀ b ∈ [a], ∀ i, b.displacement i=(b.service.target.symm i : ℤ)-(i : ℤ) := by
    intro b hb i
    exact congrFun (hcan b hb) i
  have hb : FiniteRankOrder.Below p (([a].map (fun s => s.service.target)).prod) := by
    rw [hprod]
    exact (joined_components_prices p hc).1
  obtain ⟨w,he,_,_,_,hl⟩ := arbitrary_finite_route_rank_transfer hn [a] hpair hc' p hb start finish
  have hcost : BufferProgram.rotations (route start finish ([a].map ExactService.service))=
      BufferProgram.rotations a.service.word+
        (min (port-start).val (n-(port-start).val)+min (finish-port).val (n-(finish-port).val)) := by
    simp [route_rotations,walkCost,ha]
  rw [hcost] at hl
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.cast_zero,sub_zero] at hrot
  have hl' : (w.length : ℤ)=(inversionNumber p : ℤ)+(BufferProgram.rotations a.service.word : ℤ)+
      (min (port-start).val (n-(port-start).val)+min (finish-port).val (n-(finish-port).val) : ℕ) := by
    exact_mod_cast hl.trans (Nat.add_assoc _ _ _).symm
  exact ⟨w,he,by omega⟩

#print axioms joined_incident_word
end LRX.FiniteCuts
