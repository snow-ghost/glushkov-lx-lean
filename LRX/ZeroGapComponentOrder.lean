import LRX.ZeroGapTouchedInterior

/-! The final event index in each component strictly decreases whenever an
arrow touches a different component. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

noncomputable def componentTime (events : List (Event n)) (root : Fin n) : ℕ := by
  classical
  exact Finset.univ.sup (fun t : Fin events.length =>
    if EventReaches events root (events.get t).1 then t.val+1 else 0)

theorem component_time_eq {events : List (Event n)} {i j : Fin n}
    (h : EventReaches events i j) : componentTime events i=componentTime events j := by
  classical
  have heq : ∀ x, EventReaches events i x ↔ EventReaches events j x :=
    fun x => ⟨fun hx => (event_reaches_symm events h).trans hx,fun hx => h.trans hx⟩
  unfold componentTime
  simp only [heq]

theorem event_time_le {events : List (Event n)} (t : Fin events.length) {i : Fin n}
    (hr : EventReaches events i (events.get t).1) : t.val+1 ≤ componentTime events i := by
  classical
  have h := Finset.le_sup (f := fun s : Fin events.length =>
    if EventReaches events i (events.get s).1 then s.val+1 else 0) (Finset.mem_univ t)
  simpa only [if_pos hr,componentTime] using h

theorem contained_component_time_lt {events : List (Event n)}
    (hsep : events.Pairwise LaterOutside) (t : Fin events.length) {i j : Fin n}
    (hi : EventReaches events i (events.get t).1)
    (hj : ∀ x, EventReaches events j x → Inside (events.get t) x) :
    componentTime events j < componentTime events i := by
  classical
  have hbound : componentTime events j ≤ t.val := by
    apply Finset.sup_le
    intro s hs
    split_ifs with hr
    · have hin := hj _ hr
      have hst : s < t := by
        by_contra hn
        rcases lt_or_eq_of_le (le_of_not_gt hn) with hts | hts
        · exact (hsep.rel_get_of_lt hts).1 hin
        · subst s
          simpa [Inside,distance] using hin
      exact hst
    · exact Nat.zero_le _
  exact lt_of_le_of_lt hbound (lt_of_lt_of_le (Nat.lt_succ_self _) (event_time_le t hi))

theorem Travel.other_component_time_lt {events : List (Event n)}
    (hsep : events.Pairwise LaterOutside) {i j b : Fin n} {z : ℤ}
    (hp : Travel events i j z)
    (ht : BufferProgram.Touches (n : ℤ) (i : ℤ) z (b : ℤ))
    (hother : ¬EventReaches events i b) : componentTime events b < componentTime events i := by
  obtain ⟨e,he,hr,hinside⟩ := hp.touched_other_component hsep ht hother
  obtain ⟨t,ht⟩ := List.mem_iff_get.mp he
  subst e
  exact contained_component_time_lt hsep t hr hinside

#print axioms Travel.other_component_time_lt
end LRX.ZeroGap
