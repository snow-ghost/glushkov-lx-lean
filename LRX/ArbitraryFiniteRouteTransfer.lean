import LRX.ArbitraryPortRankTransfer
import LRX.FiniteRouteRankTransfer

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem eval_identity_base (w : List Letter) (base : Configuration n)
    (ht : base.physical.tokens=1) :
    eval w=(RotationWords.rotation base.physical.cursor)⁻¹*
      (run w base).physical.tokens*RotationWords.rotation (run w base).physical.cursor := by
  have he := PhysicalModel.visible_run w base.physical
  rw [← run_physical] at he
  change (run w base).physical.tokens*RotationWords.rotation (run w base).physical.cursor=
    base.physical.tokens*RotationWords.rotation base.physical.cursor*eval w at he
  rw [ht,one_mul] at he
  calc
    eval w=(RotationWords.rotation base.physical.cursor)⁻¹*
      (RotationWords.rotation base.physical.cursor*eval w) := by group
    _ = _ := by rw [← he]; group
end LRX.LiftedModel

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem arbitrary_finite_route_rank_transfer (hn : 2 ≤ n) (ss : List (ExactService n))
    (hd : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : ∀ a ∈ ss, ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ))
    (p : State n) (hp : FiniteRankOrder.Below p (ss.map (fun a => a.service.target)).prod)
    (start finish : Fin n) :
    ∃ v : List Letter, eval v=(rotation start)⁻¹*p*rotation finish ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters (route start finish (ss.map ExactService.service)) ∧
      (∀ i, (LiftedModel.run v (LiftedModel.atPort start (start : ℤ))).position i=(p.symm i : ℤ)) ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber p ∧
      v.length=FiniteCuts.inversionNumber p+
        BufferProgram.rotations (route start finish (ss.map ExactService.service)) := by
  let base := LiftedModel.atPort start (start : ℤ)
  let w := route start finish (ss.map ExactService.service)
  let q := (ss.map (fun a : ExactService n => a.service.target)).prod
  have hbase : LiftedModel.Aligned base := by
    constructor
    · simp [base,LiftedModel.atPort]
    · intro i
      simp [base,LiftedModel.atPort]
      rfl
  have hpos : ∀ i, (LiftedModel.run w base).position i=(q.symm i : ℤ) := by
    intro i
    have he := exact_route_positions ss hd start finish base rfl
      (by intro a ha; simp [base,LiftedModel.atPort]) i
    rw [exact_canonical_route_displacement ss hd hcan i] at he
    change (LiftedModel.run w base).position i=(i : ℤ)+((q.symm i : ℤ)-(i : ℤ)) at he
    linarith
  have hcur : (LiftedModel.run w base).physical.cursor=finish := by
    have ha := (LiftedModel.run_aligned hn w hbase).1
    have hr := route_cursor start finish (ss.map ExactService.service) base
      (by simp [base,LiftedModel.atPort])
    exact ha.symm.trans hr
  have ht : (LiftedModel.run w base).physical.tokens=q := by
    have he := LiftedModel.eval_identity_base w base rfl
    rw [hcur] at he
    have heval : eval w=(rotation start)⁻¹*q*rotation finish := by
      simp only [w,route_eval,q,List.map_map,Function.comp_def]
    rw [heval] at he
    change (rotation start)⁻¹*q*rotation finish=
      (rotation start)⁻¹*(LiftedModel.run w base).physical.tokens*rotation finish at he
    exact (mul_left_cancel (mul_right_cancel he)).symm
  obtain ⟨v,hrot,hcursor,htokens,hpositions,hx,hlen⟩ :=
    LiftedModel.forward_finite_rank_transfer_from hn w p q base rfl (fun _ => rfl) hbase hp ht hpos
  have hvcur : (LiftedModel.run v base).physical.cursor=finish := by
    have ha := (LiftedModel.run_aligned hn v hbase).1
    rw [hcursor] at ha
    have hb := (LiftedModel.run_aligned hn w hbase).1
    exact ha.symm.trans (hb.trans hcur)
  refine ⟨v,?_,hrot,hpositions,hx,hlen⟩
  rw [LiftedModel.eval_identity_base v base rfl,htokens,hvcur]
  rfl

#print axioms arbitrary_finite_route_rank_transfer
end LRX.RotationWords
