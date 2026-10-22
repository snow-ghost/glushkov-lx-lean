import LRX.OutsideCyclePositivePort
import LRX.CanonicalServiceFamily

/-! A selected list of actual outside cycles supplies canonical exact
services, one per cycle, each with a rotation saving of at least two. -/
namespace LRX.ZeroGap
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem outside_cycle_service_family (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0)
    (hroot : p⁻¹ 0 ≠ 0) (cycles : List (State n))
    (hc : ∀ q ∈ cycles, q ∈ outsideCycles p d 0) :
    ∃ services : List (ExactService n),
      services.map (fun a => a.service.target)=cycles.map (fun q => q⁻¹) ∧
      services.length=cycles.length ∧ CanonicalFamily services ∧
      (∀ a ∈ services, ∃ q ∈ cycles, a.service.port=cycleRoot q) ∧
      (∀ a ∈ services, (BufferProgram.rotations a.service.word : ℤ) ≤
        (∑ i : Fin n, |a.displacement i|)-2) := by
  induction cycles with
  | nil => exact ⟨[],rfl,rfl,by intro a ha; simp at ha,by simp,by simp⟩
  | cons q rest ih =>
    have hq := hc q (by simp)
    obtain ⟨a,ha,ht,hdisp,hprice⟩ := outside_cycle_paid_service hn hd hcover hroot hq
    obtain ⟨ss,hst,hlen,hcan,hports,hprices⟩ := ih (fun t ht => hc t (List.mem_cons_of_mem _ ht))
    have hca : a.displacement=(fun i => (a.service.target.symm i : ℤ)-(i : ℤ)) := by
      rw [hdisp,outside_cycle_displacement hd hcover hroot hq,ht]
      rfl
    refine ⟨a::ss,by simp [ht,hst],by simp [hlen],?_,?_,?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hca
      · exact hcan b hb
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨q,by simp,ha⟩
      · obtain ⟨t,ht,hport⟩ := hports b hb
        exact ⟨t,List.mem_cons_of_mem _ ht,hport⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa only [hdisp] using hprice
      · exact hprices b hb

#print axioms outside_cycle_service_family
end LRX.ZeroGap
