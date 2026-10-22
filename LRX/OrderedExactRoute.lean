import LRX.ReducedServiceRoute
import LRX.OrderedPortRoute

/-! Sorting exact services preserves their lifted endpoint and permits an
interval bound after affine deletion of the combined route. -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

theorem exists_ordered_exact_services (services : List (ExactService n)) :
    ∃ ordered : List (ExactService n), services.Perm ordered ∧
      ordered.Pairwise (fun a b => a.service.port.val ≤ b.service.port.val) := by
  let le : ExactService n → ExactService n → Bool := fun a b => a.service.port.val ≤ b.service.port.val
  refine ⟨services.mergeSort le, (List.mergeSort_perm services le).symm, ?_⟩
  simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using List.pairwise_mergeSort (le := le)
    (fun a b c hab hbc => by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_trans (by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using hab) (by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using hbc))
    (fun a b => by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total a.service.port.val b.service.port.val) services

theorem ordered_reduced_route (hn : 2 ≤ n) (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (finish : Fin n) (hports : ∀ a ∈ services, a.service.port.val ≤ finish.val) :
    ∃ w : List Letter,
      eval w=(services.map (fun a => a.service.target)).prod*rotation finish ∧
      w.length ≤ LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+(services.map (fun a => a.displacement i)).sum)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+finish.val := by
  obtain ⟨ordered, hp, ho⟩ := exists_ordered_exact_services services
  have hd : ordered.Pairwise (fun a b => a.service.target.Disjoint b.service.target) :=
    (hp.pairwise_iff (fun h => h.symm)).mp hdis
  obtain ⟨w, he, _, hl⟩ := reduced_service_route hn ordered hd finish
  have htarget : (services.map (fun a => a.service.target)).prod=
      (ordered.map (fun a => a.service.target)).prod :=
    Equiv.Perm.disjoint_prod_perm (List.pairwise_map.mpr hdis)
      (hp.map (fun a => a.service.target))
  have hend : (fun i : Fin n => (i : ℤ)+(ordered.map (fun a => a.displacement i)).sum)=
      (fun i : Fin n => (i : ℤ)+(services.map (fun a => a.displacement i)).sum) := by
    funext i
    rw [(hp.map (fun a => a.displacement i)).sum_eq]
  have hw : walkCost 0 finish (ordered.map ExactService.service) ≤ finish.val := by
    have h := ordered_walk_cost 0 finish (ordered.map ExactService.service) (by simp)
      (List.pairwise_map.mpr ho) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact ⟨Nat.zero_le _, hports b (hp.mem_iff.mpr hb)⟩)
    simpa using h
  refine ⟨w, ?_, ?_⟩
  · rw [htarget]; exact he
  · rw [hl, hend, ← (hp.map (fun a => BufferProgram.rotations a.service.word)).sum_eq]
    omega

#print axioms ordered_reduced_route
end LRX.RotationWords
