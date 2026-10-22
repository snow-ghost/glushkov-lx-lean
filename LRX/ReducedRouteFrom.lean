import LRX.PortEndpointInverse
import LRX.ReducedServiceRoute

/-! Affine reduction for a service route with arbitrary initial cursor.
The inversion price remains that of the original balanced lift. -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

theorem reduced_route_from (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (ht : (services.map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ i, (services.map (fun a => a.displacement i)).sum=d i)
    (start finish : Fin n) :
    ∃ w : List Letter,
      eval w=(rotation start)⁻¹*p*rotation finish ∧
      w.length=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+
        walkCost start finish (services.map ExactService.service) := by
  let raw := route start finish (services.map ExactService.service)
  have hport : ∀ i, (LiftedModel.run raw (LiftedModel.atPort start 0)).position i=(i : ℤ)+d i := by
    intro i
    have h := exact_route_positions services hdis start finish (LiftedModel.atPort start 0) rfl
      (fun a _ => Equiv.Perm.disjoint_one_right _) i
    simpa only [LiftedModel.atPort,hdisp] using h
  have hend : (LiftedModel.run raw (LiftedModel.initial (n := n))).position=
      (fun i : Fin n => (i : ℤ)+localDisplacement d start i) :=
    funext (LiftedModel.initial_endpoints_of_port raw start 0 d hport)
  obtain ⟨w,_,he,_,_,hlen,_⟩ := LiftedModel.affine_reduction_exact hn raw
  rw [hend,inversion_count_recentered 0 start (by simpa using hd)] at hlen
  refine ⟨w,?_,?_⟩
  · rw [he]
    simp only [raw,route_eval,List.map_map,Function.comp_def,ht]
  · rw [hlen]
    simp only [raw,route_rotations,List.map_map,Function.comp_def]
    omega

#print axioms reduced_route_from
end LRX.RotationWords
