import LRX.ZeroGapComponentSize
import Mathlib

/-! If a list of roots meets every event component, the number of vertices
is at most the number of exchange events plus the number of roots. -/
namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

def liftEvent (e : Event n) : Event (n+1) := (e.1.succ,e.2.succ)

def rootedEvents (events : List (Event n)) (roots : List (Fin n)) : List (Event (n+1)) :=
  events.map liftEvent ++ roots.map (fun r => (0,r.succ))

theorem event_edge_lift {events : List (Event n)} (roots : List (Fin n))
    {i j : Fin n} (he : EventEdge events i j) :
    EventEdge (rootedEvents events roots) i.succ j.succ := by
  obtain ⟨e,he,h⟩ := he
  refine ⟨liftEvent e,List.mem_append_left _ (List.mem_map.mpr ⟨e,he,rfl⟩),?_⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩

theorem event_reaches_lift {events : List (Event n)} (roots : List (Fin n))
    {i j : Fin n} (hp : EventReaches events i j) :
    EventReaches (rootedEvents events roots) i.succ j.succ := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.tail (event_edge_lift roots he)

theorem root_cover_count (events : List (Event n)) (roots : List (Fin n))
    (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i) :
    n ≤ events.length+roots.length := by
  classical
  have hreach : ∀ i : Fin (n+1), EventReaches (rootedEvents events roots) 0 i := by
    intro i
    refine Fin.cases Relation.ReflTransGen.refl (fun j => ?_) i
    obtain ⟨r,hr,hp⟩ := hcover j
    have hedge : EventEdge (rootedEvents events roots) 0 r.succ :=
      ⟨(0,r.succ),List.mem_append_right _ (List.mem_map.mpr ⟨r,hr,rfl⟩),Or.inl ⟨rfl,rfl⟩⟩
    exact (Relation.ReflTransGen.single hedge).trans (event_reaches_lift roots hp)
  have hfull : eventComponent (rootedEvents events roots) 0=Finset.univ := by
    ext i
    simp only [mem_eventComponent,Finset.mem_univ,iff_true]
    exact hreach i
  have hsize := event_component_size (rootedEvents events roots) 0
  rw [hfull] at hsize
  simp only [Finset.card_univ,Fintype.card_fin,rootedEvents,List.length_append,List.length_map] at hsize
  omega

#print axioms root_cover_count
end LRX.ZeroGap
