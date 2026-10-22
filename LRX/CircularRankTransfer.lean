import LRX.CircularOrderedRoute
import LRX.ArbitraryFiniteRouteTransfer
import LRX.CanonicalServiceFamily

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem circular_rank_transfer_route (hn : 2 ≤ n) (p : State n)
    (forward : Bool) (start finish : Fin n) (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily services)
    (hbelow : FiniteRankOrder.Below p ((services.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ services, (arcCoordinate forward start a.service.port).val ≤
      (arcCoordinate forward start finish).val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ inversionNumber p+(services.map (fun a => BufferProgram.rotations a.service.word)).sum+
        (arcCoordinate forward start finish).val := by
  obtain ⟨ordered,hperm,ho⟩ := arc_ordered_services forward start services
  have hdo : ordered.Pairwise (fun a b => a.service.target.Disjoint b.service.target) :=
    (hperm.pairwise_iff (fun h => h.symm)).mp hdis
  have hbo : FiniteRankOrder.Below p ((ordered.map (fun a => a.service.target)).prod) := by
    rw [← Equiv.Perm.disjoint_prod_perm (List.pairwise_map.mpr hdis)
      (hperm.map (fun a => a.service.target))]
    exact hbelow
  have hco : ∀ a ∈ ordered, ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ) := by
    intro a ha i
    exact congrFun (hcan a (hperm.mem_iff.mpr ha)) i
  obtain ⟨w,he,_,_,_,hl⟩ := arbitrary_finite_route_rank_transfer hn ordered hdo hco p hbo start finish
  have hz : arcCoordinate forward start start=0 := by cases forward <;> simp [arcCoordinate]
  have hw := arc_walk_cost forward start start finish (ordered.map ExactService.service)
    (by rw [hz]; exact Nat.zero_le _) (List.pairwise_map.mpr ho) (by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact ⟨by rw [hz]; exact Nat.zero_le _,hrange b (hperm.mem_iff.mpr hb)⟩)
  rw [hz,Fin.val_zero,Nat.sub_zero] at hw
  have hrot := (hperm.map (fun a => BufferProgram.rotations a.service.word)).sum_eq
  have hcost := route_rotations start finish (ordered.map ExactService.service)
  simp only [List.map_map,Function.comp_def] at hcost
  exact ⟨w,he,by omega⟩

#print axioms circular_rank_transfer_route
end LRX.FiniteCuts
