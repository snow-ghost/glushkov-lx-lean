import LRX.ZeroGapEventGraph
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ}

def eventEdgeKey (e : Event n) : Sym2 (Fin n) := Sym2.mk e.1 e.2

/-- Select each prescribed undirected edge once, preserving the order of actual events. -/
theorem select_event_edges (events : List (Event n)) (T : Finset (Sym2 (Fin n)))
    (hT : T ⊆ (events.map eventEdgeKey).toFinset) :
    ∃ part : List (Event n), part.Sublist events ∧
      (part.map eventEdgeKey).Nodup ∧ (part.map eventEdgeKey).toFinset=T ∧ part.length=T.card := by
  classical
  let chosen := ((events.map eventEdgeKey).filter (fun e => decide (e ∈ T))).dedup
  have hsub : chosen.Sublist (events.map eventEdgeKey) :=
    (List.dedup_sublist _).trans List.filter_sublist
  obtain ⟨part,hpart,he⟩ := List.sublist_map_iff.mp hsub
  have hn : chosen.Nodup := List.nodup_dedup _
  have hset : chosen.toFinset=T := by
    ext e
    simp only [List.mem_toFinset,chosen,List.mem_dedup,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨List.mem_toFinset.mp (hT h),h⟩⟩
  have hlen : chosen.length=T.card := by
    rw [← hset,List.toFinset_card_of_nodup hn]
  rw [he] at hn hset hlen
  rw [List.length_map] at hlen
  exact ⟨part,hpart,hn,hset,hlen⟩

theorem event_edge_key_iff (events : List (Event n)) (i j : Fin n) :
    Sym2.mk i j ∈ (events.map eventEdgeKey).toFinset ↔ EventEdge events i j := by
  classical
  simp only [List.mem_toFinset,List.mem_map,eventEdgeKey,Sym2.eq_iff,EventEdge]
  constructor
  · rintro ⟨e,he,⟨hi,hj⟩ | ⟨hi,hj⟩⟩
    · exact ⟨e,he,Or.inl ⟨hi.symm,hj.symm⟩⟩
    · exact ⟨e,he,Or.inr ⟨hj.symm,hi.symm⟩⟩
  · rintro ⟨e,he,⟨hi,hj⟩ | ⟨hi,hj⟩⟩
    · exact ⟨e,he,Or.inl ⟨hi.symm,hj.symm⟩⟩
    · exact ⟨e,he,Or.inr ⟨hj.symm,hi.symm⟩⟩

#print axioms select_event_edges
end LRX.ZeroGap
