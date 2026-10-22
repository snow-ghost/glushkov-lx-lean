import LRX.CycleNeighborFromEvents

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Arbitrary edge weights of a minimal event tree admit a vertex potential. -/
theorem minimal_event_potential (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) (weight : Event n → ℤ) :
    ∃ H : Fin n → ℤ, ∀ e ∈ events, H e.2-H e.1=weight e := by
  classical
  have main : ∀ m : ℕ, ∀ (xs : List (Event n)) (r : Fin n), xs.length=m →
      xs.length+1=(eventComponent xs r).card →
      ∃ H : Fin n → ℤ, ∀ e ∈ xs, H e.2-H e.1=weight e := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro xs r hlen hm
      cases xs with
      | nil => exact ⟨fun _ => 0,by simp⟩
      | cons e rest =>
        have hr := minimal_events_reachable (e::rest) r hm e (by simp)
        have heq := event_component_reroot (e::rest) hr
        have hm' : (e::rest).length+1=(eventComponent (e::rest) e.1).card := by rwa [← heq]
        have hbranches := head_branch_minimal e rest hm'
        have hlt (b : Fin n) : (componentEvents rest b).length < m := by
          have hl : (componentEvents rest b).length ≤ rest.length := List.length_filter_le _ _
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨A,hA⟩ := ih (componentEvents rest e.1).length (hlt e.1) (componentEvents rest e.1) e.1 rfl
          (by rw [selected_component_eq]; exact hbranches.1)
        obtain ⟨B,hB⟩ := ih (componentEvents rest e.2).length (hlt e.2) (componentEvents rest e.2) e.2 rfl
          (by rw [selected_component_eq]; exact hbranches.2)
        have hab := head_endpoints_disconnected e rest hm'
        have hba : ¬EventReaches rest e.2 e.1 := fun h => hab (event_reaches_symm rest h)
        let H : Fin n → ℤ := fun i => if EventReaches rest e.2 i
          then B i+A e.1+weight e-B e.2 else A i
        refine ⟨H,?_⟩
        intro f hf
        rcases List.mem_cons.mp hf with hf | hf
        · subst f
          have hb : EventReaches rest e.2 e.2 := Relation.ReflTransGen.refl
          simp only [H,if_neg hba,if_pos hb]
          ring
        · have hreach := minimal_events_reachable (e::rest) e.1 hm' f (List.mem_cons_of_mem e hf)
          have hedge : EventEdge rest f.1 f.2 := ⟨f,hf,Or.inl ⟨rfl,rfl⟩⟩
          rcases head_components_cover e rest hreach with ha | hb
          · have ha' := ha.tail hedge
            have hn0 : ¬EventReaches rest e.2 f.1 := fun h => hab (ha.trans (event_reaches_symm rest h))
            have hn1 : ¬EventReaches rest e.2 f.2 := fun h => hab (ha'.trans (event_reaches_symm rest h))
            have hp := hA f (by simp [componentEvents,hf,ha])
            simpa only [H,if_neg hn0,if_neg hn1] using hp
          · have hb' := hb.tail hedge
            have hp := hB f (by simp [componentEvents,hf,hb])
            dsimp [H]
            rw [if_pos hb,if_pos hb']
            linarith
  exact main events.length events root rfl hmin

theorem Travel.potential {events : List (Event n)} (H : Fin n → ℤ)
    (hH : ∀ e ∈ events, H e.2-H e.1=(distance e.1 e.2 : ℤ))
    {i j : Fin n} {z : ℤ} (ht : Travel events i j z) : H j-H i=z := by
  induction ht with
  | refl => simp
  | @head i j k a b he hp ih =>
    obtain ⟨e,he,hor⟩ := he
    have hw := hH e he
    rcases hor with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> linarith

#print axioms minimal_event_potential
#print axioms Travel.potential
end LRX.ZeroGap
