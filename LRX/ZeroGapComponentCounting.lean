import LRX.ZeroGapComponentSize
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

noncomputable def componentEvents (events : List (Event n)) (root : Fin n) : List (Event n) := by
  classical
  exact events.filter (fun e => decide (EventReaches events root e.1))

noncomputable def outsideEvents (events : List (Event n)) (root : Fin n) : List (Event n) := by
  classical
  exact events.filter (fun e => decide (¬EventReaches events root e.1))

theorem component_events_length (events : List (Event n)) (root : Fin n) :
    (componentEvents events root).length+(outsideEvents events root).length=events.length := by
  classical
  simp only [componentEvents,outsideEvents,decide_not]
  have hsplit : ∀ (xs : List (Event n)) (f : Event n → Bool),
      (xs.filter f).length+(xs.filter (fun e => !f e)).length=xs.length := by
    intro xs f
    induction xs with
    | nil => rfl
    | cons e rest ih => cases hf : f e <;> simp [hf] <;> omega
  exact hsplit events _

theorem component_edge_selected {events : List (Event n)} {root i j : Fin n}
    (hi : EventReaches events root i) (he : EventEdge events i j) :
    EventEdge (componentEvents events root) i j := by
  classical
  obtain ⟨e,he,h⟩ := he
  have hr : EventReaches events root e.1 := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hi
    · exact hi.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  exact ⟨e,by simp [componentEvents,he,hr],h⟩

theorem component_selected_size (events : List (Event n)) (root : Fin n) :
    (eventComponent events root).card ≤ (componentEvents events root).length+1 := by
  classical
  let G := componentGraph events root
  have hvertices := (component_graph_connected events root).card_vert_le_card_edgeSet_add_one
  have hedges := graph_edges_le_events G (componentEvents events root) Subtype.val
    Subtype.val_injective (fun i j h => component_edge_selected
      ((mem_eventComponent events root i.val).mp i.property) h.2)
  have hcard : Nat.card {i : Fin n // i ∈ eventComponent events root}=(eventComponent events root).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  change Nat.card {i : Fin n // i ∈ eventComponent events root} ≤ Nat.card G.edgeSet+1 at hvertices
  rw [hcard] at hvertices
  omega

def endpoints (events : List (Event n)) : Finset (Fin n) :=
  (events.flatMap (fun e => [e.1,e.2])).toFinset

@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]

theorem endpoints_card (events : List (Event n)) : (endpoints events).card ≤ 2*events.length := by
  have h := List.toFinset_card_le (events.flatMap (fun e => [e.1,e.2]))
  have hlen : (events.flatMap (fun e => [e.1,e.2])).length=2*events.length := by
    induction events with
    | nil => simp
    | cons e rest ih => simp [ih]; omega
  exact h.trans_eq hlen

theorem event_product_fixed (events : List (Event n)) (i : Fin n)
    (hi : i ∉ endpoints events) : (events.map eventSwap).prod i=i := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    have hneq : i ≠ e.1 ∧ i ≠ e.2 := by
      constructor <;> intro h <;> apply hi <;> simp [mem_endpoints,h]
    have hrest : i ∉ endpoints rest := by
      intro h
      apply hi
      obtain ⟨f,hf,h⟩ := (mem_endpoints rest i).mp h
      exact (mem_endpoints (e::rest) i).mpr ⟨f,List.mem_cons_of_mem _ hf,h⟩
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply,ih hrest,eventSwap]
    exact Equiv.swap_apply_of_ne_of_ne hneq.1 hneq.2


end LRX.ZeroGap
