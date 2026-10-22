import LRX.EventTreeBranchCounts

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

theorem selected_reaches_iff (events : List (Event n)) (root i : Fin n) :
    EventReaches (componentEvents events root) root i ↔ EventReaches events root i := by
  classical
  constructor
  · apply event_reaches_mono
    intro e he
    exact (List.mem_filter.mp he).1
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail (component_edge_selected hp he)

theorem selected_component_eq (events : List (Event n)) (root : Fin n) :
    eventComponent (componentEvents events root) root=eventComponent events root := by
  ext i
  simp only [mem_eventComponent,selected_reaches_iff]

/-- Restricting the event list to one component preserves the product on
that component. This connects the inductive arrow to the original word. -/
theorem selected_product_agrees (events : List (Event n)) (root i : Fin n)
    (hi : EventReaches events root i) :
    ((componentEvents events root).map eventSwap).prod i=(events.map eventSwap).prod i := by
  classical
  have main : ∀ part : List (Event n), (∀ e ∈ part, e ∈ events) →
      ∀ j : Fin n, EventReaches events root j →
      (((part.filter (fun e => decide (EventReaches events root e.1))).map eventSwap).prod j)=
        (part.map eventSwap).prod j := by
    intro part
    induction part with
    | nil => intro _ j _; rfl
    | cons e rest ih =>
      intro hsub j hj
      have he : e ∈ events := hsub e (by simp)
      have hs : ∀ f ∈ rest, f ∈ events := fun f hf => hsub f (List.mem_cons_of_mem _ hf)
      have hp := ih hs j hj
      have hreach : EventReaches events root ((rest.map eventSwap).prod j) :=
        hj.trans (event_product_reaches events rest hs j)
      by_cases hsel : EventReaches events root e.1
      · simp [List.filter_cons,hsel,List.map_cons,List.prod_cons,
          Equiv.Perm.mul_apply,hp]
      · have hne0 : (rest.map eventSwap).prod j ≠ e.1 := fun h => hsel (h ▸ hreach)
        have hne1 : (rest.map eventSwap).prod j ≠ e.2 := by
          intro h
          have he' : EventEdge events e.2 e.1 := ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
          exact hsel ((h ▸ hreach).tail he')
        simp [List.filter_cons,hsel,List.map_cons,List.prod_cons,
          Equiv.Perm.mul_apply,hp,eventSwap,Equiv.swap_apply_of_ne_of_ne hne0 hne1]
  exact main events (fun _ h => h) i hi

#print axioms selected_component_eq
#print axioms selected_product_agrees
end LRX.ZeroGap
