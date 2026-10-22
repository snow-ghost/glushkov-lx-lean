import LRX.ZeroGapEventGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! An event list bounds the number of distinct graph edges, including for
an induced graph on a subset of physical positions. -/
namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

theorem graph_edges_le_events {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (events : List (Event n)) (f : α → Fin n) (hf : Function.Injective f)
    (hedge : ∀ i j, G.Adj i j → EventEdge events (f i) (f j)) :
    Nat.card G.edgeSet ≤ events.length := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hmem : ∀ q, q ∈ G.edgeFinset → Sym2.map f q ∈ events.toFinset.image (fun e => Sym2.mk e.1 e.2) := by
    intro q
    refine Sym2.inductionOn q ?_
    intro i j hq
    have ha : G.Adj i j := (G.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp hq)
    obtain ⟨e,he,h⟩ := hedge i j ha
    apply Finset.mem_image.mpr
    refine ⟨e,List.mem_toFinset.mpr he,?_⟩
    rcases h with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · simpa only [Sym2.map_mk,hi,hj]
    · simpa only [Sym2.map_mk,hi,hj] using (Sym2.eq_swap (a := e.1) (b := e.2))
  have hsub : G.edgeFinset.image (Sym2.map f) ⊆ events.toFinset.image (fun e => Sym2.mk e.1 e.2) := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
    exact hmem e he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (Sym2.map.injective hf)] at hc
  have hl : (events.toFinset.image (fun e => Sym2.mk e.1 e.2)).card ≤ events.length :=
    Finset.card_image_le.trans (List.toFinset_card_le events)
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  exact hc.trans hl

#print axioms graph_edges_le_events
end LRX.ZeroGap
