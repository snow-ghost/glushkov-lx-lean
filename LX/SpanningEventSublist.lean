import LX.EventTreeBranchCounts
import LX.SelectedEventEdges
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- An actual event component admits an order-preserving spanning tree subsequence. -/
theorem component_spanning_event_sublist (events : List (Event n)) (root : Fin n) :
    ∃ part : List (Event n), part.Sublist events ∧
      eventComponent part root = eventComponent events root ∧
      part.length+1 = (eventComponent events root).card ∧
      (∀ e ∈ part, e.1 ≠ e.2) ∧ (part.map eventEdgeKey).Nodup := by
  classical
  let C := {i : Fin n // i ∈ eventComponent events root}
  obtain ⟨T,hTG,hTree⟩ := (component_graph_connected events root).exists_isTree_le
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let keys : Finset (Sym2 (Fin n)) := T.edgeFinset.image (Sym2.map (Subtype.val : C → Fin n))
  have hsubkeys : keys ⊆ (events.map eventEdgeKey).toFinset := by
    intro q hq
    obtain ⟨edge,hedge,rfl⟩ := Finset.mem_image.mp hq
    revert hedge
    refine Sym2.inductionOn edge ?_
    intro a b hab
    have ha : T.Adj a b := T.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hab)
    have he : EventEdge events a.val b.val := (hTG ha).2
    exact (event_edge_key_iff events a.val b.val).mpr he
  obtain ⟨part,hpart,hnodup,hkeys,hlen⟩ := select_event_edges events keys hsubkeys
  have hstep {a b : C} (hab : T.Adj a b) : EventEdge part a.val b.val := by
    apply (event_edge_key_iff part _ _).mp
    rw [hkeys]
    apply Finset.mem_image.mpr
    exact ⟨Sym2.mk a b,SimpleGraph.mem_edgeFinset.mpr (T.mem_edgeSet.mpr hab),rfl⟩
  have hreach {a b : C} (hab : T.Reachable a b) : EventReaches part a.val b.val := by
    have hh := (T.reachable_iff_reflTransGen a b).mp hab
    clear hab
    induction hh with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail (hstep he)
  have hcomp : eventComponent part root = eventComponent events root := by
    ext i
    constructor
    · intro hi
      exact (mem_eventComponent _ _ _).mpr
        (event_reaches_mono (fun e he => hpart.subset he) ((mem_eventComponent _ _ _).mp hi))
    · intro hi
      exact (mem_eventComponent _ _ _).mpr
        (hreach (hTree.connected.preconnected (rootVertex events root) ⟨i,hi⟩))
  have hcard : keys.card = T.edgeFinset.card :=
    Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
  have hsize := hTree.card_edgeFinset
  have hC : Fintype.card C = (eventComponent events root).card := Fintype.card_coe _
  change T.edgeFinset.card+1 = Fintype.card C at hsize
  rw [hC] at hsize
  have hneq : ∀ e ∈ part, e.1 ≠ e.2 := by
    intro e he hsame
    have hk : eventEdgeKey e ∈ keys := by
      rw [← hkeys]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
    obtain ⟨edge,hedge,heq⟩ := Finset.mem_image.mp hk
    revert hedge heq
    refine Sym2.inductionOn edge ?_
    intro a b hab heq
    have ha : T.Adj a b := T.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hab)
    have hh : a.val = b.val := by
      simp only [Sym2.map_mk,eventEdgeKey,Sym2.eq_iff] at heq
      rcases heq with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp_all
    exact ha.ne (Subtype.ext hh)
  refine ⟨part,hpart,hcomp,?_,hneq,hnodup⟩
  omega

#print axioms component_spanning_event_sublist
end LX.Core.ZeroGap
