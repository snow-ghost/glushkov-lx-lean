import LRX.EventNeighborInductionStep

/-! Rank neighbors from minimal separated event trees, without an external
classification of shallow cycles. The bridge from shallow defect to this
finite linear event contract remains separate. -/
namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- A minimal linear event tree on at least three vertices has a neighboring
arrow avoiding any prescribed extreme vertex of its carrier. -/
theorem minimal_tree_neighbor_away (events : List (Event n)) (root : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hmin : events.length+1=(eventComponent events root).card)
    (hcard : 3 ≤ (eventComponent events root).card)
    (hext : IsExtreme (eventComponent events root) root) : NeighborAway events root root := by
  classical
  have main : ∀ m : ℕ, ∀ (xs : List (Event n)) (r : Fin n), xs.length=m →
      (∀ e ∈ xs, e.1.val < e.2.val) → xs.Pairwise LaterOutside →
      xs.length+1=(eventComponent xs r).card → 3 ≤ (eventComponent xs r).card →
      IsExtreme (eventComponent xs r) r → NeighborAway xs r r := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro xs r hlen hl hs hm hc hx
      cases xs with
      | nil => simp only [List.length_nil] at hm; omega
      | cons e rest =>
        have hrhead := minimal_events_reachable (e::rest) r hm e (by simp)
        have hcarrier := event_component_reroot (e::rest) hrhead
        have hm' : (e::rest).length+1=(eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have hc' : 3 ≤ (eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have hx' : IsExtreme (eventComponent (e::rest) e.1) r := by rwa [← hcarrier]
        have hr' : r ∈ eventComponent (e::rest) e.1 :=
          (mem_eventComponent _ _ _).mpr (event_reaches_symm (e::rest) hrhead)
        have branches := head_branch_minimal e rest hm'
        have ih' : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent rest b).card →
            IsExtreme (eventComponent rest b) b → NeighborAway (componentEvents rest b) b b := by
          intro b hb hcb hxb
          have hle : (componentEvents rest b).length ≤ rest.length := List.length_filter_le _ _
          have hlt : (componentEvents rest b).length < m := by simp only [List.length_cons] at hlen; omega
          have hlin : ∀ f ∈ componentEvents rest b, f.1.val < f.2.val := by
            intro f hf
            exact hl f (List.mem_cons_of_mem e (List.mem_filter.mp hf).1)
          have hsep' : (componentEvents rest b).Pairwise LaterOutside := (List.pairwise_cons.mp hs).2.filter _
          have hmin' : (componentEvents rest b).length+1=(eventComponent (componentEvents rest b) b).card := by
            rw [selected_component_eq]
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
            rcases hb with rfl | rfl
            · exact branches.1
            · exact branches.2
          exact ih (componentEvents rest b).length hlt (componentEvents rest b) b rfl
            hlin hsep' hmin' (by rwa [selected_component_eq]) (by rwa [selected_component_eq])
        have hres := event_neighbor_induction_step e rest hl hs hm' hc' ih' r hr' hx'
        simpa only [NeighborAway,← hcarrier] using hres
  exact main events.length events root rfl hlinear hsep hmin hcard hext

/-- Existence of an actual arrow between adjacent carrier ranks, including
the two-vertex case. No neighboring-arrow premise remains. -/
theorem minimal_tree_rank_neighbor (events : List (Event n)) (root : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hmin : events.length+1=(eventComponent events root).card)
    (hcard : 2 ≤ (eventComponent events root).card) :
    ∃ x y, RankAdjacent (eventComponent events root) x y ∧ (events.map eventSwap).prod x=y := by
  classical
  let S := eventComponent events root
  change 2 ≤ S.card at hcard
  have hne : S.Nonempty := ⟨root,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  let a := S.min' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hr := (mem_eventComponent events root a).mp ha
  have heq := event_component_reroot events hr
  by_cases hc2 : S.card=2
  · obtain ⟨x,y,hxy,hp,_⟩ := minimal_two_vertex_neighbor events root hmin hlinear hc2 root
      ((mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl)
    exact ⟨x,y,hxy,hp⟩
  · have h3 : 3 ≤ (eventComponent events a).card := by rw [← heq]; change 3 ≤ S.card; omega
    have hx : IsExtreme (eventComponent events a) a := by
      left
      intro i hi
      rw [← heq] at hi
      exact Finset.min'_le S i hi
    obtain ⟨x,y,hxy,hp,_,_⟩ := minimal_tree_neighbor_away events a hlinear hsep
      (by rwa [← heq]) h3 hx
    exact ⟨x,y,by rwa [← heq] at hxy,hp⟩

#print axioms minimal_tree_neighbor_away
#print axioms minimal_tree_rank_neighbor
end LRX.ZeroGap
