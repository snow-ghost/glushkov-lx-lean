import LRX.MinimalEventCarrier

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

def IsExtreme (S : Finset (Fin n)) (r : Fin n) : Prop :=
  (∀ i ∈ S, r.val ≤ i.val) ∨ (∀ i ∈ S, i.val ≤ r.val)

theorem rank_adjacent_symm {S : Finset (Fin n)} {a b : Fin n}
    (h : RankAdjacent S a b) : RankAdjacent S b a := by
  refine ⟨h.2.1,h.1,Ne.symm h.2.2.1,?_⟩
  intro i hi
  simpa only [min_comm,max_comm] using h.2.2.2 i hi

/-- The branch opposite an excluded extreme is an interval, and its
attachment vertex is an extreme of that branch. All geometric conditions
needed for the smaller induction are derived here. -/
theorem opposite_branch_interval (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (S : Finset (Fin n)) (a b r : Fin n)
    (hab : ¬EventReaches events a b) (har : EventReaches events a r)
    (hsub : eventComponent events b ⊆ S)
    (hcover : ∀ i ∈ S, EventReaches events a i ∨ EventReaches events b i)
    (hext : IsExtreme S r) (hgap : RankAdjacent S a b) :
    CarrierInterval (eventComponent events b) S ∧ IsExtreme (eventComponent events b) b := by
  classical
  let T := eventComponent events b
  have hne : T.Nonempty := ⟨b,(mem_eventComponent events b b).mpr Relation.ReflTransGen.refl⟩
  let lo := T.min' hne
  let hi := T.max' hne
  have hlo : lo ∈ T := Finset.min'_mem T hne
  have hhi : hi ∈ T := Finset.max'_mem T hne
  have hb_lo := (mem_eventComponent events b lo).mp hlo
  have hb_hi := (mem_eventComponent events b hi).mp hhi
  have heq : T=eventComponent events lo := event_component_reroot events hb_lo
  have hbound (i : Fin n) (hip : EventReaches events lo i) : lo.val ≤ i.val ∧ i.val ≤ hi.val := by
    have him : i ∈ T := (mem_eventComponent events b i).mpr (hb_lo.trans hip)
    exact ⟨Finset.min'_le T i him,Finset.le_max' T i him⟩
  have hnot : ¬EventReaches events lo r := by
    intro h
    exact hab ((har.trans (event_reaches_symm events h)).trans (event_reaches_symm events hb_lo))
  have hrlo : r ≠ lo := by intro h; subst r; exact hnot Relation.ReflTransGen.refl
  have hrhi : r ≠ hi := by intro h; subst r; exact hnot ((event_reaches_symm events hb_lo).trans hb_hi)
  have hout : r.val < lo.val ∨ hi.val < r.val := by
    have hnlo : r.val ≠ lo.val := fun h => hrlo (Fin.ext h)
    have hnhi : r.val ≠ hi.val := fun h => hrhi (Fin.ext h)
    rcases hext with h | h
    · have := h lo (hsub hlo); left; omega
    · have := h hi (hsub hhi); right; omega
  have hlh : EventReaches events lo hi := (event_reaches_symm events hb_lo).trans hb_hi
  have hc : ∀ i ∈ S, EventReaches events lo i ∨ EventReaches events r i := by
    intro i him
    rcases hcover i him with h | h
    · exact Or.inr ((event_reaches_symm events har).trans h)
    · exact Or.inl ((event_reaches_symm events hb_lo).trans h)
  have hinterval := component_interval_of_two_cover events hlinear hsep lo hi r hlh hbound hnot hout S
    (by rw [← heq]; exact hsub) hc
  have hboundary := adjacent_attachment_boundary events hlinear hsep lo hi r a b hlh hbound hnot hout
    (event_reaches_symm events har) (event_reaches_symm events hb_lo)
    (fun i hip => hgap.2.2.2 i (hsub ((mem_eventComponent events b i).mpr (hb_lo.trans hip))))
  refine ⟨?_,?_⟩
  · simpa only [← heq] using hinterval
  · rcases hboundary with hb | hb
    · left
      intro i him
      rw [hb]
      exact (hbound i ((event_reaches_symm events hb_lo).trans ((mem_eventComponent events b i).mp him))).1
    · right
      intro i him
      rw [hb]
      exact (hbound i ((event_reaches_symm events hb_lo).trans ((mem_eventComponent events b i).mp him))).2

#print axioms opposite_branch_interval
end LRX.ZeroGap
