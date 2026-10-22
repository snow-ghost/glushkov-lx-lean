import LRX.ForwardFiniteRankTransfer
import LRX.ExactServiceRoute
import LRX.FiniteDisplacementSum
import LRX.FiniteCycleScan

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem eval_initial_tokens (w : List Letter) :
    eval w=(run w (initial (n:=n))).physical.tokens*
      RotationWords.rotation (run w (initial (n:=n))).physical.cursor := by
  have he := PhysicalModel.visible_run w (initial (n:=n)).physical
  rw [← run_physical,show PhysicalModel.visible (initial (n:=n)).physical=1 from rfl,one_mul] at he
  exact he.symm
end LRX.LiftedModel

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exact_canonical_route_displacement (ss : List (ExactService n))
    (hd : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : ∀ a ∈ ss, ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    (ss.map (fun a => a.displacement i)).sum=
      (((ss.map (fun a : ExactService n => a.service.target)).prod.symm i : Fin n) : ℤ)-(i : ℤ) := by
  let l := ss.map (fun a : ExactService n => a.service.target)
  have hdis : l.Pairwise Equiv.Perm.Disjoint := List.pairwise_map.mpr hd
  have hc := FiniteCuts.displacement_list_prod (l.map (fun p => p⁻¹))
    (FiniteCuts.inverse_targets_disjoint l hdis) i
  rw [FiniteCuts.inverse_cycle_product l hdis] at hc
  have he : ss.map (fun a => a.displacement i)=
      ss.map (fun a => FiniteCuts.displacement a.service.target⁻¹ i) := by
    apply List.map_congr_left
    intro a ha
    exact hcan a ha i
  rw [he]
  simpa only [l,List.map_map,Function.comp_def,FiniteCuts.displacement,Equiv.Perm.inv_def] using hc.symm

/-- Apply exact rank transfer to the already constructed route of actual
closed services. Individual services have canonical finite endpoints. -/
theorem finite_route_rank_transfer (hn : 2 ≤ n) (ss : List (ExactService n))
    (hd : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : ∀ a ∈ ss, ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ))
    (p : State n) (hp : FiniteRankOrder.Below p (ss.map (fun a : ExactService n => a.service.target)).prod)
    (finish : Fin n) :
    ∃ v : List Letter, eval v=p*rotation finish ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters (route 0 finish (ss.map ExactService.service)) ∧
      (∀ i, (LiftedModel.run v (LiftedModel.initial (n:=n))).position i=(p.symm i : ℤ)) ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber p ∧
      v.length=FiniteCuts.inversionNumber p+
        BufferProgram.rotations (route 0 finish (ss.map ExactService.service)) := by
  let w := route 0 finish (ss.map ExactService.service)
  let q := (ss.map (fun a : ExactService n => a.service.target)).prod
  have hpos : ∀ i, (LiftedModel.run w (LiftedModel.initial (n:=n))).position i=(q.symm i : ℤ) := by
    intro i
    have he := exact_route_positions ss hd 0 finish (LiftedModel.initial (n:=n)) rfl
      (by intro a ha; simp [LiftedModel.initial,PhysicalModel.initial]) i
    rw [exact_canonical_route_displacement ss hd hcan i] at he
    change (LiftedModel.run w (LiftedModel.initial (n:=n))).position i=
      (i : ℤ)+((q.symm i : ℤ)-(i : ℤ)) at he
    linarith
  have hcur : (LiftedModel.run w (LiftedModel.initial (n:=n))).physical.cursor=finish := by
    have ha := (LiftedModel.run_aligned hn w LiftedModel.initial_aligned).1
    have hr := route_cursor 0 finish (ss.map ExactService.service) (LiftedModel.initial (n:=n)) (by simp [LiftedModel.initial])
    exact ha.symm.trans hr
  have ht : (LiftedModel.run w (LiftedModel.initial (n:=n))).physical.tokens=q := by
    have he := LiftedModel.eval_initial_tokens (n:=n) w
    rw [hcur] at he
    have heval : eval w=q*rotation finish := by
      simp [w,q,route_eval,List.map_map,Function.comp_def,rotation]
    rw [heval] at he
    exact mul_right_cancel he.symm
  obtain ⟨v,hrot,hcursor,htokens,hpositions,hx,hlen⟩ :=
    LiftedModel.forward_finite_rank_transfer hn w p q hp ht hpos
  have hvcur : (LiftedModel.run v (LiftedModel.initial (n:=n))).physical.cursor=finish := by
    have ha := (LiftedModel.run_aligned hn v LiftedModel.initial_aligned).1
    rw [hcursor] at ha
    have hb := (LiftedModel.run_aligned hn w LiftedModel.initial_aligned).1
    exact ha.symm.trans (hb.trans hcur)
  refine ⟨v,?_,hrot,hpositions,hx,hlen⟩
  rw [LiftedModel.eval_initial_tokens,htokens,hvcur]

#print axioms finite_route_rank_transfer
end LRX.RotationWords
