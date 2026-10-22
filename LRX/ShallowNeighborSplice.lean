import LRX.LinearEventComponents

namespace LRX.ZeroGap
variable {n : ℕ}

/-- Adjacency in the ordered carrier, allowing either arrow direction. -/
def RankAdjacent (S : Finset (Fin n)) (x y : Fin n) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
    ∀ z ∈ S, ¬(min x.val y.val < z.val ∧ z.val < max x.val y.val)

/-- An interval relative to an ordered carrier; fixed ambient positions may
lie in its gaps. -/
def CarrierInterval (T S : Finset (Fin n)) : Prop :=
  T ⊆ S ∧ ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ S,
    min x.val y.val < z.val → z.val < max x.val y.val → z ∈ T

theorem rank_adjacent_of_interval {T S : Finset (Fin n)} (hT : CarrierInterval T S)
    {x y : Fin n} (hxy : RankAdjacent T x y) : RankAdjacent S x y := by
  refine ⟨hT.1 hxy.1,hT.1 hxy.2.1,hxy.2.2.1,?_⟩
  intro z hz hz'
  exact hxy.2.2.2 z (hT.2 x hxy.1 y hxy.2.1 z hz hz'.1 hz'.2) hz'

theorem head_rank_adjacent [NeZero n] (e : Event n) (events : List (Event n))
    (he : e.1.val < e.2.val) (hsep : (e::events).Pairwise LaterOutside) :
    RankAdjacent (eventComponent (e::events) e.1) e.1 e.2 := by
  have hfirst : e.1 ∈ eventComponent (e::events) e.1 :=
    (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  have hsecond : e.2 ∈ eventComponent (e::events) e.1 :=
    (mem_eventComponent _ _ _).mpr (Relation.ReflTransGen.single ⟨e,by simp,Or.inl ⟨rfl,rfl⟩⟩)
  refine ⟨hfirst,hsecond,fun h => (by have := congrArg Fin.val h; omega),?_⟩
  intro z hz hz'
  have hins : Inside e z := (inside_linear_iff e he z).mpr (by
    simpa only [min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)] using hz')
  have hnot : z ∉ endpoints (e::events) := by
    intro hm
    obtain ⟨f,hf,hzf⟩ := (mem_endpoints _ _).mp hm
    rcases List.mem_cons.mp hf with hf | hf
    · subst f
      rcases hzf with hzf | hzf
      · subst z; have h := hins.1; simp [distance] at h
      · subst z; exact lt_irrefl _ hins.2
    · have h := (List.pairwise_cons.mp hsep).1 f hf
      rcases hzf with hzf | hzf
      · exact h.1 (hzf ▸ hins)
      · exact h.2 (hzf ▸ hins)
  have hp := (mem_eventComponent (e::events) e.1 z).mp hz
  have hr : z=e.1 ∨ z ∈ endpoints (e::events) := by
    induction hp with
    | refl => exact Or.inl rfl
    | @tail u v hp hv ih =>
      right
      obtain ⟨f,hf,hor⟩ := hv
      apply (mem_endpoints _ _).mpr
      exact ⟨f,hf,hor.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)⟩
  rcases hr with hr | hr
  · subst z
    have h := hins.1
    simp [distance] at h
  · exact hnot hr

theorem component_interval_of_two_cover [NeZero n] (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (S : Finset (Fin n)) (hsub : eventComponent events lo ⊆ S)
    (hcover : ∀ i ∈ S, EventReaches events lo i ∨ EventReaches events root i) :
    CarrierInterval (eventComponent events lo) S := by
  refine ⟨hsub,?_⟩
  intro x hx y hy z hz hzx hzy
  have hxb := hbound x ((mem_eventComponent events lo x).mp hx)
  have hyb := hbound y ((mem_eventComponent events lo y).mp hy)
  rcases hcover z hz with h | h
  · exact (mem_eventComponent events lo z).mpr h
  · have hnot := component_cannot_enter_hull events hlinear hsep lo hi root
      hlohi hbound havoid hout z h
    exact False.elim (hnot (by omega))

/-- The two-vertex base case gives a neighboring arrow whose target avoids
any prescribed carrier vertex. -/
theorem two_vertex_neighbor_avoids_target (p : State n) (hcard : p.support.card=2)
    (r : Fin n) (hr : r ∈ p.support) :
    ∃ x y : Fin n, RankAdjacent p.support x y ∧ p x=y ∧ y ≠ r := by
  classical
  have hne : p r ≠ r := Equiv.Perm.mem_support.mp hr
  have hpr : p r ∈ p.support := by
    apply Equiv.Perm.mem_support.mpr
    intro h
    exact hne (p.injective h)
  have hsub : ({r,p r} : Finset (Fin n)) ⊆ p.support := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hpair : ({r,p r} : Finset (Fin n))=p.support := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hcard,Ne.symm hne]
  refine ⟨r,p r,⟨hr,hpr,Ne.symm hne,?_⟩,rfl,hne⟩
  intro z hz hbetween
  rw [← hpair] at hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> omega

/-- A neighboring arrow in an interval branch survives restoration of a
head exchange, provided its target avoids the attachment vertex. The
excluded outer vertex is absent from both ends of the resulting arrow. -/
theorem splice_neighbor_from_interval (q : State n) (T S : Finset (Fin n))
    (hT : CarrierInterval T S) (a b excluded : Fin n)
    (ha : a ∉ T) (hexcluded : excluded ∉ T)
    (hneighbor : ∃ x y : Fin n, RankAdjacent T x y ∧ q x=y ∧ y ≠ b) :
    ∃ x y : Fin n, RankAdjacent S x y ∧ (Equiv.swap a b*q) x=y ∧
      x ≠ excluded ∧ y ≠ excluded := by
  obtain ⟨x,y,hxy,hq,hyb⟩ := hneighbor
  have hya : y ≠ a := fun h => ha (h ▸ hxy.2.1)
  refine ⟨x,y,rank_adjacent_of_interval hT hxy,?_,?_,?_⟩
  · rw [Equiv.Perm.mul_apply,hq,Equiv.swap_apply_of_ne_of_ne hya hyb]
  · intro h
    exact hexcluded (h ▸ hxy.1)
  · intro h
    exact hexcluded (h ▸ hxy.2.1)

#print axioms head_rank_adjacent
#print axioms component_interval_of_two_cover
#print axioms two_vertex_neighbor_avoids_target
#print axioms splice_neighbor_from_interval
end LRX.ZeroGap
