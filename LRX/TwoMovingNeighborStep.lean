import LRX.ExtremeEventBranch

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

def NeighborAway (events : List (Event n)) (root r : Fin n) : Prop :=
  ∃ x y, RankAdjacent (eventComponent events root) x y ∧
    (events.map eventSwap).prod x=y ∧ x ≠ r ∧ y ≠ r

theorem minimal_tree_safe_neighbor (events : List (Event n)) (root r : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : 2 ≤ (eventComponent events root).card) (hr : r ∈ eventComponent events root)
    (ih : 3 ≤ (eventComponent events root).card → NeighborAway events root r) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧
      (events.map eventSwap).prod x=y ∧ y ≠ r := by
  by_cases htwo : (eventComponent events root).card=2
  · exact minimal_two_vertex_neighbor events root hmin hlinear htwo r hr
  · obtain ⟨x,y,hxy,hp,_,hy⟩ := ih (by omega)
    exact ⟨x,y,hxy,hp,hy⟩

/-- The complete two-moving-branches step. The only inductive inputs are
neighbor statements for smaller, already selected branches. -/
theorem opposite_moving_neighbor_step (e : Event n) (events : List (Event n))
    (hlinear : ∀ f ∈ e::events, f.1.val < f.2.val)
    (hsep : (e::events).Pairwise LaterOutside)
    (hmin : (e::events).length+1=(eventComponent (e::events) e.1).card)
    (r : Fin n)
    (ha : EventReaches events e.2 r → 2 ≤ (eventComponent events e.1).card)
    (hb : EventReaches events e.1 r → 2 ≤ (eventComponent events e.2).card)
    (ih : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent events b).card →
      IsExtreme (eventComponent events b) b → NeighborAway (componentEvents events b) b b)
    (hr : r ∈ eventComponent (e::events) e.1)
    (hext : IsExtreme (eventComponent (e::events) e.1) r) :
    NeighborAway (e::events) e.1 r := by
  classical
  let S := eventComponent (e::events) e.1
  have hab := head_endpoints_disconnected e events hmin
  have hba : ¬EventReaches events e.2 e.1 := fun h => hab (event_reaches_symm events h)
  have hm := head_branch_minimal e events hmin
  have hl : ∀ f ∈ events, f.1.val < f.2.val := fun f hf => hlinear f (List.mem_cons_of_mem e hf)
  have hs := (List.pairwise_cons.mp hsep).2
  have hgap := head_rank_adjacent e events (hlinear e (by simp)) hsep
  have hcover (i : Fin n) (hi : i ∈ S) :
      EventReaches events e.1 i ∨ EventReaches events e.2 i :=
    head_components_cover e events ((mem_eventComponent _ _ _).mp hi)
  have hsubA : eventComponent events e.1 ⊆ S := by
    dsimp [S]; rw [head_component_union]; exact Finset.subset_union_left
  have hsubB : eventComponent events e.2 ⊆ S := by
    dsimp [S]; rw [head_component_union]; exact Finset.subset_union_right
  have safe (b : Fin n) (hbm : b ∈ [e.1,e.2])
      (hmb : (componentEvents events b).length+1=(eventComponent events b).card)
      (hcb : 2 ≤ (eventComponent events b).card) (hxb : IsExtreme (eventComponent events b) b) :
      ∃ x y, RankAdjacent (eventComponent events b) x y ∧
        (events.map eventSwap).prod x=y ∧ y ≠ b := by
    have hlin : ∀ f ∈ componentEvents events b, f.1.val < f.2.val :=
      fun f hf => hl f (List.mem_filter.mp hf).1
    obtain ⟨x,y,hxy,hp,hy⟩ := minimal_tree_safe_neighbor (componentEvents events b) b b
      (by rwa [selected_component_eq]) hlin (by rwa [selected_component_eq])
      ((mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl)
      (fun h => ih b hbm (by rwa [selected_component_eq] at h) hxb)
    rw [selected_component_eq] at hxy
    have hx := (mem_eventComponent events b x).mp hxy.1
    exact ⟨x,y,hxy,(selected_product_agrees events b x hx).symm.trans hp,hy⟩
  rcases hcover r hr with har | hbr
  · obtain ⟨hinterval,hboundary⟩ := opposite_branch_interval events hl hs S e.1 e.2 r
      hab har hsubB hcover hext hgap
    have hna : e.1 ∉ eventComponent events e.2 := fun h => hba ((mem_eventComponent _ _ _).mp h)
    have hnr : r ∉ eventComponent events e.2 := fun h =>
      hab (har.trans (event_reaches_symm events ((mem_eventComponent _ _ _).mp h)))
    obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := splice_neighbor_from_interval (events.map eventSwap).prod
      (eventComponent events e.2) S hinterval e.1 e.2 r hna hnr (safe e.2 (by simp) hm.2 (hb har) hboundary)
    exact ⟨x,y,hxy,by simpa only [List.map_cons,List.prod_cons,eventSwap] using hp,hxr,hyr⟩
  · obtain ⟨hinterval,hboundary⟩ := opposite_branch_interval events hl hs S e.2 e.1 r
      hba hbr hsubA (fun i hi => (hcover i hi).symm) hext (rank_adjacent_symm hgap)
    have hna : e.2 ∉ eventComponent events e.1 := fun h => hab ((mem_eventComponent _ _ _).mp h)
    have hnr : r ∉ eventComponent events e.1 := fun h =>
      hba (hbr.trans (event_reaches_symm events ((mem_eventComponent _ _ _).mp h)))
    obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := splice_neighbor_from_interval (events.map eventSwap).prod
      (eventComponent events e.1) S hinterval e.2 e.1 r hna hnr (safe e.1 (by simp) hm.1 (ha hbr) hboundary)
    exact ⟨x,y,hxy,by simpa only [List.map_cons,List.prod_cons,eventSwap,Equiv.swap_comm e.2 e.1] using hp,hxr,hyr⟩

#print axioms opposite_moving_neighbor_step
end LRX.ZeroGap
