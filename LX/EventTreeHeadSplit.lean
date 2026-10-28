import LX.ZeroGapComponentSize
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Removing one event leaves every originally reachable vertex in one of
the two endpoint components. -/
theorem head_components_cover (e : Event n) (events : List (Event n)) {i : Fin n}
    (hi : EventReaches (e::events) e.1 i) :
    EventReaches events e.1 i ∨ EventReaches events e.2 i := by
  induction hi with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail u v hp he ih =>
    obtain ⟨f,hf,h⟩ := he
    rcases List.mem_cons.mp hf with hf | hf
    · subst f
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr Relation.ReflTransGen.refl
      · exact Or.inl Relation.ReflTransGen.refl
    · have he : EventEdge events u v := ⟨f,hf,h⟩
      exact ih.elim (fun h => Or.inl (h.tail he)) (fun h => Or.inr (h.tail he))

/-- Minimal event count forces the first event to join different tail
components. This avoids assuming the graph is a tree as a new premise. -/
theorem head_endpoints_disconnected (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    ¬EventReaches events e.1 e.2 := by
  intro hab
  have hsub : eventComponent (e::events) e.1 ⊆ eventComponent events e.1 := by
    intro i hi
    apply (mem_eventComponent events e.1 i).mpr
    have h := head_components_cover e events ((mem_eventComponent (e::events) e.1 i).mp hi)
    exact h.elim id (fun h => hab.trans h)
  have hcard := Finset.card_le_card hsub
  have htail := event_component_size events e.1
  simp only [List.length_cons] at hminimal
  omega

theorem head_component_disjoint (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    Disjoint (eventComponent events e.1) (eventComponent events e.2) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact head_endpoints_disconnected e events hminimal
    (((mem_eventComponent events e.1 i).mp hi).trans
      (event_reaches_symm events ((mem_eventComponent events e.2 i).mp hj)))

#print axioms head_components_cover
#print axioms head_endpoints_disconnected
#print axioms head_component_disjoint
end LX.Core.ZeroGap
