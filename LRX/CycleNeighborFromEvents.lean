import LRX.EventTreeRankNeighbor

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

theorem cycle_event_carrier {p : State n} (hp : p.IsCycle)
    (events : List (Event n)) (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (root : Fin n) (hr : root ∈ p.support) : eventComponent events root=p.support := by
  classical
  ext i
  rw [mem_eventComponent]
  constructor
  · intro hi
    induction hi with
    | refl => exact hr
    | tail hpath he ih =>
      obtain ⟨e,he,hor⟩ := he
      have ha := hactive e he
      rcases hor with h | h
      · exact h.2.symm ▸ ha.2
      · exact h.2.symm ▸ ha.1
  · intro hi
    have hr' : p⁻¹ root ≠ root := Equiv.Perm.mem_support.mp (by simpa using hr)
    have hi' : p⁻¹ i ≠ i := Equiv.Perm.mem_support.mp (by simpa using hi)
    exact cycle_event_reachable events p hprod (hp.inv.sameCycle hr' hi')

/-- The rank-neighbor conclusion for a cycle from its minimal linear
sorting events. Its carrier is proved equal to the actual cycle support. -/
theorem cycle_neighbor_of_events {p : State n} (hp : p.IsCycle)
    (events : List (Event n)) (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlen : events.length+1=p.support.card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside) :
    ∃ x y, RankAdjacent p.support x y ∧ p x=y := by
  classical
  obtain ⟨root,hr⟩ := hp.nonempty_support
  have hc := cycle_event_carrier hp events hprod hactive root hr
  obtain ⟨x,y,hxy,harrow⟩ := minimal_tree_rank_neighbor events root hlinear hsep
    (by rwa [hc]) (by rw [hc]; exact hp.two_le_card_support)
  exact ⟨x,y,by rwa [hc] at hxy,by rwa [hprod] at harrow⟩

#print axioms cycle_event_carrier
#print axioms cycle_neighbor_of_events
end LRX.ZeroGap
