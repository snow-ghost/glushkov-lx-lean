import LRX.ZeroGapComponentCounting

/-! The event-graph route toward the rank-neighbor consequence for shallow
cycles. These lemmas do not assume a separable-permutation classification. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem minimal_component_is_tree (events : List (Event n)) (root : Fin n)
    (hminimal : (componentEvents events root).length+1=(eventComponent events root).card) :
    (componentGraph events root).IsTree := by
  classical
  let G := componentGraph events root
  have hc := component_graph_connected events root
  have hv := hc.card_vert_le_card_edgeSet_add_one
  have he := graph_edges_le_events G (componentEvents events root) Subtype.val
    Subtype.val_injective (fun i j h => component_edge_selected
      ((mem_eventComponent events root i.val).mp i.property) h.2)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events root}=(eventComponent events root).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc,?_⟩
  apply Nat.le_antisymm
  · rw [hcard]
    exact (Nat.add_le_add_right he 1).trans_eq hminimal
  · exact hv

theorem head_inside_fixed (e : Event n) (events : List (Event n))
    (hsep : (e::events).Pairwise LaterOutside) (i : Fin n) (hi : Inside e i) :
    ((e::events).map eventSwap).prod i=i := by
  apply event_product_fixed
  intro hm
  obtain ⟨f,hf,hif⟩ := (mem_endpoints (e::events) i).mp hm
  rcases List.mem_cons.mp hf with hf | hf
  · subst f
    rcases hif with hif | hif
    · subst i
      have h := hi.1
      simp [distance] at h
    · subst i
      exact (lt_irrefl _ hi.2)
  · have h := (List.pairwise_cons.mp hsep).1 f hf
    rcases hif with hif | hif
    · exact h.1 (hif ▸ hi)
    · exact h.2 (hif ▸ hi)

/-- No support vertex lies inside the first event arc. This is adjacency
of event endpoints, not yet an arrow of the final permutation. -/
theorem head_inside_not_support (e : Event n) (events : List (Event n))
    (hsep : (e::events).Pairwise LaterOutside) (i : Fin n) (hi : Inside e i) :
    i ∉ ((e::events).map eventSwap).prod.support := by
  simpa only [Equiv.Perm.mem_support,not_not] using head_inside_fixed e events hsep i hi

/-- If deletion of the first event leaves one endpoint fixed, that event
is an actual arrow of the original permutation. The two-moving-branches
case needs a separate tree argument. -/
theorem head_arrow_of_fixed_endpoint (e : Event n) (events : List (Event n))
    (hfix : (events.map eventSwap).prod e.1=e.1 ∨
      (events.map eventSwap).prod e.2=e.2) :
    ((e::events).map eventSwap).prod e.1=e.2 ∨
      ((e::events).map eventSwap).prod e.2=e.1 := by
  rcases hfix with hfix | hfix
  · left
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply,hfix,eventSwap,
      Equiv.swap_apply_left]
  · right
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply,hfix,eventSwap,
      Equiv.swap_apply_right]

#print axioms head_arrow_of_fixed_endpoint
#print axioms minimal_component_is_tree
#print axioms head_inside_not_support
end LRX.ZeroGap
