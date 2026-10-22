import LRX.ClosedServiceAction

/-! Exact endpoints of a paid route through disjoint closed services. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

structure ExactService (n : ℕ) [NeZero n] where
  service : ClosedService n
  displacement : Fin n → ℤ
  stationary : ∀ i, service.target i=i → displacement i=0
  endpoint : ∀ z i, (LiftedModel.run service.word
    (LiftedModel.atPort service.port z)).position i=(i : ℤ)+displacement i

theorem to_port_physical_cursor (r : Fin n) (s : LiftedModel.Configuration n) :
    (LiftedModel.run (toPort r) s).physical.cursor=s.physical.cursor+r := by
  rw [LiftedModel.physical_cursor_run]
  simp only [toPort, spin_increment, short_offset_cast]

theorem exact_route_positions (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (start finish : Fin n) (s : LiftedModel.Configuration n)
    (hport : s.physical.cursor=start)
    (hframe : ∀ a ∈ services, a.service.target.Disjoint s.physical.tokens) :
    ∀ i, (LiftedModel.run (route start finish (services.map ExactService.service)) s).position i=
      s.position i+(services.map (fun a => a.displacement i)).sum := by
  induction services generalizing start s with
  | nil =>
    intro i
    simp only [List.map_nil, route, toPort, spin_positions, List.sum_nil, add_zero]
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdis
    let entered := LiftedModel.run (toPort (a.service.port-start)) s
    have heport : entered.physical.cursor=a.service.port := by
      dsimp [entered]
      rw [to_port_physical_cursor, hport]
      abel
    have hetokens : entered.physical.tokens=s.physical.tokens := spin_tokens _ _
    have hepos : entered.position=s.position := spin_positions _ _
    let completed := LiftedModel.run a.service.word entered
    have hcport : completed.physical.cursor=a.service.port :=
      (closed_service_cursor a.service entered).2.trans heport
    have hctokens : completed.physical.tokens=s.physical.tokens*a.service.target := by
      dsimp [completed]
      rw [closed_service_tokens a.service entered heport, hetokens]
    have hcpos (i : Fin n) : completed.position i=s.position i+a.displacement i := by
      have h := LiftedModel.disjoint_service_action a.service.word a.service.port a.displacement
        a.endpoint a.service.target a.stationary entered heport
        (by rw [hetokens]; exact hframe a (by simp)) i
      exact h.trans (by rw [hepos])
    have hf : ∀ b ∈ rest, b.service.target.Disjoint completed.physical.tokens := by
      intro b hb
      rw [hctokens]
      exact (hframe b (by simp [hb])).mul_right (hhead b hb).symm
    have hrest := ih htail a.service.port completed hcport hf
    intro i
    simp only [List.map_cons, route, LiftedModel.run_append]
    change (LiftedModel.run (route a.service.port finish (rest.map ExactService.service)) completed).position i= _
    rw [hrest, hcpos]
    simp only [List.sum_cons]
    ring

#print axioms exact_route_positions
end LRX.RotationWords
