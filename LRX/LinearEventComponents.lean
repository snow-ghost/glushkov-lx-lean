import LRX.ShallowEventTree

/-! Separation of components in a finite, linearly oriented event forest.
The linear-orientation hypothesis is explicit; a circular trace needs an
appropriate zero-load cut before these statements can be applied. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem inside_linear_iff (e : Event n) (he : e.1.val < e.2.val) (i : Fin n) :
    Inside e i ↔ e.1.val < i.val ∧ i.val < e.2.val := by
  unfold Inside distance
  rw [Fin.sub_val_of_le (show e.1 ≤ e.2 from le_of_lt he)]
  by_cases hi : e.1 ≤ i
  · rw [Fin.sub_val_of_le hi]
    change e.1.val ≤ i.val at hi
    omega
  · have hil : i<e.1 := lt_of_not_ge hi
    rw [Fin.coe_sub_iff_lt.mpr hil]
    have hn := e.2.isLt
    change i.val < e.1.val at hil
    omega

/-- A path straddling a vertex in another component has an edge whose
open interval contains that vertex. -/
theorem event_path_straddles (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (a b z : Fin n)
    (ha : a.val < b.val) (havoid : ¬EventReaches events a b)
    (hp : EventReaches events a z) (hz : b.val < z.val) :
    ∃ e ∈ events, EventReaches events a e.1 ∧ EventReaches events a e.2 ∧ Inside e b := by
  induction hp with
  | refl => omega
  | @tail u v hp hedge ih =>
    by_cases hu : u.val < b.val
    · obtain ⟨e,he,hor⟩ := hedge
      refine ⟨e,he,?_,?_,(inside_linear_iff e (hlinear e he) b).mpr ?_⟩
      · rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hp
        · exact hp.tail ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
      · rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hp.tail ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
        · exact hp
      · rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hu,hz⟩
        · have := hlinear e he
          omega
    · have hne : u.val ≠ b.val := by
        intro he
        have he' : u=b := Fin.ext he
        exact havoid (he' ▸ hp)
      exact ih (by omega)

/-- If one component crosses a vertex of another, the latter component
lies strictly inside the hull of the former. -/
theorem component_inside_hull (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (a b z : Fin n) (ha : a.val < b.val) (hz : b.val < z.val)
    (haz : EventReaches events a z) (havoid : ¬EventReaches events a b)
    (lo hi : ℕ) (hbound : ∀ i, EventReaches events a i → lo ≤ i.val ∧ i.val ≤ hi)
    (j : Fin n) (hbj : EventReaches events b j) : lo < j.val ∧ j.val < hi := by
  obtain ⟨e,he,hea,heb,heinside⟩ := event_path_straddles events hlinear a b z ha havoid haz hz
  have hn : ¬EventReaches events b e.1 ∧ ¬EventReaches events b e.2 := by
    constructor
    · intro h
      exact havoid (hea.trans (event_reaches_symm events h))
    · intro h
      exact havoid (heb.trans (event_reaches_symm events h))
  have hj := component_inside_arc events hsep e he b heinside hn hbj
  have hji := (inside_linear_iff e (hlinear e he) j).mp hj
  have hleft := hbound e.1 hea
  have hright := hbound e.2 heb
  omega

/-- A different component with a vertex outside a component hull cannot
have a vertex strictly inside that hull. -/
theorem component_cannot_enter_hull (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (j : Fin n) (hrj : EventReaches events root j) :
    ¬(lo.val < j.val ∧ j.val < hi.val) := by
  intro hj
  have hnot : ¬EventReaches events lo j := by
    intro h
    exact havoid (h.trans (event_reaches_symm events hrj))
  have h := component_inside_hull events hlinear hsep lo j hi hj.1 hj.2
    hlohi hnot lo.val hi.val hbound root (event_reaches_symm events hrj)
  omega

/-- When an edge joins consecutive support vertices, its endpoint in an
interval component must be an extreme vertex of that component. -/
theorem adjacent_attachment_boundary (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (lo hi root a b : Fin n) (hlohi : EventReaches events lo hi)
    (hbound : ∀ i, EventReaches events lo i → lo.val ≤ i.val ∧ i.val ≤ hi.val)
    (havoid : ¬EventReaches events lo root)
    (hout : root.val < lo.val ∨ hi.val < root.val)
    (hra : EventReaches events root a) (hlob : EventReaches events lo b)
    (hgap : ∀ i, EventReaches events lo i →
      ¬(min a.val b.val < i.val ∧ i.val < max a.val b.val)) : b=lo ∨ b=hi := by
  have hna := component_cannot_enter_hull events hlinear hsep lo hi root hlohi hbound havoid hout a hra
  have ha0 : a ≠ lo := by
    intro he
    subst a
    exact havoid (event_reaches_symm events hra)
  have ha1 : a ≠ hi := by
    intro he
    subst a
    exact havoid (hlohi.trans (event_reaches_symm events hra))
  have hv0 : a.val ≠ lo.val := fun h => ha0 (Fin.ext h)
  have hv1 : a.val ≠ hi.val := fun h => ha1 (Fin.ext h)
  have hb := hbound b hlob
  have hg0 := hgap lo Relation.ReflTransGen.refl
  have hg1 := hgap hi hlohi
  by_cases hleft : a.val < lo.val
  · left
    apply Fin.ext
    omega
  · right
    apply Fin.ext
    omega

#print axioms component_cannot_enter_hull
#print axioms adjacent_attachment_boundary
#print axioms event_path_straddles
#print axioms component_inside_hull
end LRX.ZeroGap
