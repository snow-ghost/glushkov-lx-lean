import LX.ShallowNeighborSplice
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_component_reroot (events : List (Event n)) {a b : Fin n}
    (hab : EventReaches events a b) : eventComponent events a=eventComponent events b := by
  ext i
  simp only [mem_eventComponent]
  exact ⟨fun h => (event_reaches_symm events hab).trans h,fun h => hab.trans h⟩

theorem minimal_events_reachable (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    ∀ e ∈ events, EventReaches events root e.1 := by
  classical
  have hc := component_selected_size events root
  have hl : (componentEvents events root).length ≤ events.length := List.length_filter_le _ _
  have heq : (componentEvents events root).length=events.length := by omega
  have h := List.length_filter_eq_length_iff.mp heq
  intro e he
  exact of_decide_eq_true (h e he)

theorem minimal_product_support_subset (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    (events.map eventSwap).prod.support ⊆ eventComponent events root := by
  classical
  intro i hi
  by_contra hnot
  have hne : i ∉ endpoints events := by
    intro hm
    obtain ⟨e,he,hor⟩ := (mem_endpoints events i).mp hm
    have hroot := minimal_events_reachable events root hmin e he
    apply hnot
    apply (mem_eventComponent events root i).mpr
    rcases hor with rfl | rfl
    · exact hroot
    · exact hroot.tail ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  exact (Equiv.Perm.mem_support.mp hi) (event_product_fixed events i hne)

theorem minimal_two_vertex_support (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : (eventComponent events root).card=2) :
    (events.map eventSwap).prod.support=eventComponent events root := by
  classical
  have hlen : events.length=1 := by omega
  have hp : (events.map eventSwap).prod.support.card=2 := by
    obtain ⟨e,rfl⟩ := List.length_eq_one_iff.mp hlen
    have he := hlinear e (by simp)
    have hne : e.1 ≠ e.2 := by intro h; have := congrArg Fin.val h; omega
    simpa [eventSwap] using Equiv.Perm.card_support_swap hne
  exact Finset.eq_of_subset_of_card_le (minimal_product_support_subset events root hmin) (by omega)

theorem minimal_two_vertex_neighbor (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hcard : (eventComponent events root).card=2)
    (r : Fin n) (hr : r ∈ eventComponent events root) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧
      (events.map eventSwap).prod x=y ∧ y ≠ r := by
  have hs := minimal_two_vertex_support events root hmin hlinear hcard
  obtain ⟨x,y,hxy,hp,hy⟩ := two_vertex_neighbor_avoids_target
    (events.map eventSwap).prod (by rw [hs]; exact hcard) r (by rwa [hs])
  exact ⟨x,y,by rwa [hs] at hxy,hp,hy⟩

#print axioms minimal_events_reachable
#print axioms minimal_two_vertex_neighbor
end LX.Core.ZeroGap
