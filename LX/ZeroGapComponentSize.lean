import LX.ZeroGapEventEdgeCount
import Mathlib

/-! Every connected component of the event graph uses at least one fewer
exchange events than its number of vertices. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def componentGraph (events : List (Event n)) (root : Fin n) :
    SimpleGraph {i : Fin n // i ∈ eventComponent events root} where
  Adj i j := i ≠ j ∧ EventEdge events i.val j.val
  symm := by constructor; intro i j h; exact ⟨Ne.symm h.1,event_edge_symm events h.2⟩
  loopless := by constructor; intro i h; exact h.1 rfl

noncomputable def rootVertex (events : List (Event n)) (root : Fin n) :
    {i : Fin n // i ∈ eventComponent events root} :=
  ⟨root,(mem_eventComponent events root root).mpr Relation.ReflTransGen.refl⟩

theorem component_root_path (events : List (Event n)) (root : Fin n) {j : Fin n}
    (hp : EventReaches events root j) :
    (componentGraph events root).Reachable (rootVertex events root)
      ⟨j,(mem_eventComponent events root j).mpr hp⟩ := by
  induction hp with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v hp he ih =>
    by_cases huv : u=v
    · subst v
      exact ih
    · have ha : (componentGraph events root).Adj
          ⟨u,(mem_eventComponent events root u).mpr hp⟩
          ⟨v,(mem_eventComponent events root v).mpr (hp.tail he)⟩ :=
        ⟨fun h => huv (congrArg Subtype.val h),he⟩
      exact ih.trans ha.reachable

theorem component_graph_connected (events : List (Event n)) (root : Fin n) :
    (componentGraph events root).Connected := by
  letI : Nonempty {i : Fin n // i ∈ eventComponent events root} := ⟨rootVertex events root⟩
  constructor
  intro i j
  have hi := component_root_path events root ((mem_eventComponent events root i.val).mp i.property)
  have hj := component_root_path events root ((mem_eventComponent events root j.val).mp j.property)
  exact hi.symm.trans hj

theorem event_component_size (events : List (Event n)) (root : Fin n) :
    (eventComponent events root).card ≤ events.length+1 := by
  classical
  let G := componentGraph events root
  have hvertices := (component_graph_connected events root).card_vert_le_card_edgeSet_add_one
  have hedges := graph_edges_le_events G events Subtype.val Subtype.val_injective (fun i j h => h.2)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events root}=(eventComponent events root).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  change Nat.card {i : Fin n // i ∈ eventComponent events root} ≤ Nat.card G.edgeSet+1 at hvertices
  rw [hcard] at hvertices
  omega

#print axioms component_graph_connected
#print axioms event_component_size
end LX.Core.ZeroGap
