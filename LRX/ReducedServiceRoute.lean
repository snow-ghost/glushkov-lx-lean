import LRX.ExactServiceRoute
import LRX.SingleCycleServices

/-! Reachable clusters provide exact services. Affine deletion of a disjoint
service route charges the inversions of the combined endpoint, not their sum. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exists_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (r : Fin n) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p 0 r)
        (localDisplacement d r)) 0 i) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d r := by
  obtain ⟨s, hp, ht, hx, hc, he⟩ := exists_exact_closed_service hn r hd hshort hroot hreach
  have hs : ∀ i, s.target i=i → d i=0 := by
    intro i hi
    rw [ht] at hi
    apply BufferProgram.fixed_short_displacement hd i (hshort i)
    apply p.injective
    simpa using hi.symm
  have he' : ∀ z i, (LiftedModel.run s.word (LiftedModel.atPort s.port z)).position i=
      (i : ℤ)+d i := by rw [hp]; exact he
  refine ⟨⟨s, d, hs, he'⟩, hp, ht, rfl, ?_⟩
  have hlen := LiftedModel.length_eq_event_rotation s.word (LiftedModel.initial (n := n))
  rw [LiftedModel.event_count_length, hx] at hlen
  have hlen' : (s.word.length : ℤ)=
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (BufferProgram.rotations s.word : ℤ) := by exact_mod_cast hlen
  change (BufferProgram.rotations s.word : ℤ)= _
  omega

theorem single_cycle_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d r :=
  exists_exact_service hn r hd hshort hroot (cycle_root_reaches hp hd hshort r hroot)

theorem reduced_service_route (hn : 2 ≤ n) (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (finish : Fin n) :
    ∃ w : List Letter,
      eval w=(services.map (fun a => a.service.target)).prod*rotation finish ∧
      BufferProgram.exchanges w=LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+(services.map (fun a => a.displacement i)).sum) ∧
      w.length=LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+(services.map (fun a => a.displacement i)).sum)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+
        walkCost 0 finish (services.map ExactService.service) := by
  let raw := route 0 finish (services.map ExactService.service)
  have hend : (LiftedModel.run raw (LiftedModel.initial (n := n))).position=
      (fun i : Fin n => (i : ℤ)+(services.map (fun a => a.displacement i)).sum) := by
    funext i
    exact exact_route_positions services hdis 0 finish LiftedModel.initial rfl
      (fun a _ => Equiv.Perm.disjoint_one_right _) i
  obtain ⟨w, _, he, _, hx, hl, _⟩ := LiftedModel.affine_reduction_exact hn raw
  rw [hend] at hx hl
  refine ⟨w, ?_, hx, ?_⟩
  · rw [he]
    simp [raw, route_eval, rotation, List.map_map, Function.comp_def]
  · rw [hl]
    simp only [raw, route_rotations, List.map_map, Function.comp_def]
    omega

#print axioms exists_exact_service
#print axioms single_cycle_exact_service
#print axioms reduced_service_route
end LRX.RotationWords
