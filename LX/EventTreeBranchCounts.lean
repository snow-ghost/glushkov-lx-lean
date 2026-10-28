import LX.EventTreeHeadSplit
import LX.ZeroGapComponentCounting
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_reaches_mono {xs ys : List (Event n)} (hsub : ∀ e ∈ xs, e ∈ ys)
    {a b : Fin n} (hp : EventReaches xs a b) : EventReaches ys a b := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih =>
    obtain ⟨e,he,h⟩ := he
    exact ih.tail ⟨e,hsub e he,h⟩

theorem head_component_union (e : Event n) (events : List (Event n)) :
    eventComponent (e::events) e.1=eventComponent events e.1 ∪ eventComponent events e.2 := by
  ext i
  simp only [Finset.mem_union,mem_eventComponent]
  constructor
  · exact head_components_cover e events
  · intro h
    have hsub : ∀ f ∈ events, f ∈ e::events := fun f hf => List.mem_cons_of_mem e hf
    rcases h with h | h
    · exact event_reaches_mono hsub h
    · have he : EventReaches (e::events) e.1 e.2 :=
        Relation.ReflTransGen.single ⟨e,by simp,Or.inl ⟨rfl,rfl⟩⟩
      exact he.trans (event_reaches_mono hsub h)

theorem other_component_size_le_outside (events : List (Event n)) (a b : Fin n)
    (hab : ¬EventReaches events a b) :
    (eventComponent events b).card ≤ (outsideEvents events a).length+1 := by
  classical
  let G := componentGraph events b
  have hv := (component_graph_connected events b).card_vert_le_card_edgeSet_add_one
  have he := graph_edges_le_events G (outsideEvents events a) Subtype.val
    Subtype.val_injective (by
      intro i j h
      obtain ⟨e,he,hor⟩ := h.2
      have hbi := (mem_eventComponent events b i.val).mp i.property
      have hbfirst : EventReaches events b e.1 := by
        rcases hor with hh | hh
        · exact hh.1 ▸ hbi
        · have hij : EventEdge events i.val e.1 := ⟨e,he,Or.inr ⟨hh.1,rfl⟩⟩
          exact hbi.tail hij
      have hnot : ¬EventReaches events a e.1 :=
        fun h => hab (h.trans (event_reaches_symm events hbfirst))
      exact ⟨e,by simp [outsideEvents,he,hnot],hor⟩)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events b}=(eventComponent events b).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  rw [hcard] at hv
  exact hv.trans (Nat.add_le_add_right he 1)

theorem head_branch_minimal (e : Event n) (events : List (Event n))
    (hminimal : (e::events).length+1=(eventComponent (e::events) e.1).card) :
    (componentEvents events e.1).length+1=(eventComponent events e.1).card ∧
    (componentEvents events e.2).length+1=(eventComponent events e.2).card := by
  classical
  have hab := head_endpoints_disconnected e events hminimal
  have hba : ¬EventReaches events e.2 e.1 := fun h => hab (event_reaches_symm events h)
  have hdis := head_component_disjoint e events hminimal
  have hsum : (eventComponent events e.1).card+(eventComponent events e.2).card=events.length+2 := by
    rw [head_component_union,Finset.card_union_of_disjoint hdis] at hminimal
    simpa only [List.length_cons,Nat.add_assoc] using hminimal.symm
  have ha := component_selected_size events e.1
  have hb := component_selected_size events e.2
  have ha' := other_component_size_le_outside events e.1 e.2 hab
  have hb' := other_component_size_le_outside events e.2 e.1 hba
  have hla := component_events_length events e.1
  have hlb := component_events_length events e.2
  omega

#print axioms head_component_union
#print axioms other_component_size_le_outside
#print axioms head_branch_minimal
end LX.Core.ZeroGap
