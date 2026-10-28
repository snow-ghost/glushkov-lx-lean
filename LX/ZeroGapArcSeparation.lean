import LX.ZeroGapEventGraph
import Mathlib

/-! The ordered event condition gives a barrier: a different event component
cannot cross either endpoint of a chosen open event arc. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem distance_right_injective (a : Fin n) : Function.Injective (distance a) := by
  intro b c h
  exact sub_left_inj.mp (Fin.ext h)

theorem distance_pos (a b : Fin n) (h : b ≠ a) : 0 < distance a b := by
  by_contra hn
  have he : b-a=0 := Fin.ext (by change distance a b=0; omega)
  exact h (sub_eq_zero.mp he)

theorem distance_wrap (a b j : Fin n) (h : distance a b < distance a j) :
    distance j b=n+distance a b-distance a j := by
  have he : b-j=(b-a)-(j-a) := by ring
  unfold distance at *
  rw [he]
  exact Fin.coe_sub_iff_lt.mpr h

theorem crossing_visits_right (e f : Event n) (hfirst : Inside e f.1) (hlast : ¬Inside e f.2)
    (h0 : f.2 ≠ e.1) (h1 : f.2 ≠ e.2) : Inside f e.2 := by
  obtain ⟨hlo,hhi⟩ := hfirst
  have hc := distance_pos e.1 f.2 h0
  have hne : distance e.1 f.2 ≠ distance e.1 e.2 := fun h => h1 (distance_right_injective e.1 h)
  have hout : distance e.1 e.2 < distance e.1 f.2 := by unfold Inside at hlast; omega
  have hleft := distance_split e.1 e.2 f.1 (by omega)
  have hright := distance_split e.1 f.2 f.1 (by omega)
  exact ⟨by omega,by omega⟩

theorem crossing_visits_left (e f : Event n) (hlast : Inside e f.2) (hfirst : ¬Inside e f.1)
    (h0 : f.1 ≠ e.1) (h1 : f.1 ≠ e.2) : Inside f e.1 := by
  obtain ⟨hlo,hhi⟩ := hlast
  have hc := distance_pos e.1 f.1 h0
  have hne : distance e.1 f.1 ≠ distance e.1 e.2 := fun h => h1 (distance_right_injective e.1 h)
  have hout : distance e.1 e.2 < distance e.1 f.1 := by unfold Inside at hfirst; omega
  have hself : distance e.1 e.1=0 := by simp [distance]
  have hleft := distance_wrap e.1 e.1 f.1 (by rw [hself]; exact hc)
  rw [hself,Nat.add_zero] at hleft
  have hright := distance_wrap e.1 f.2 f.1 (by omega)
  have hn : distance e.1 f.1 < n := (f.1-e.1).isLt
  exact ⟨by omega,by omega⟩

theorem event_pair_order (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    {e f : Event n} (he : e ∈ events) (hf : f ∈ events) :
    e=f ∨ LaterOutside e f ∨ LaterOutside f e := by
  induction events with
  | nil => simp at he
  | cons a rest ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e
      rcases List.mem_cons.mp hf with hf | hf
      · exact Or.inl hf.symm
      · exact Or.inr (Or.inl (List.rel_of_pairwise_cons hsep hf))
    · rcases List.mem_cons.mp hf with hf | hf
      · subst f
        exact Or.inr (Or.inr (List.rel_of_pairwise_cons hsep he))
      · exact ih hsep.tail he hf

theorem event_arc_side (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    {e f : Event n} (he : e ∈ events) (hf : f ∈ events)
    (h10 : f.1 ≠ e.1) (h11 : f.1 ≠ e.2) (h20 : f.2 ≠ e.1) (h21 : f.2 ≠ e.2) :
    Inside e f.1 ↔ Inside e f.2 := by
  rcases event_pair_order events hsep he hf with h | h | h
  · subst f
    exact False.elim (h10 rfl)
  · exact ⟨fun hi => False.elim (h.1 hi),fun hi => False.elim (h.2 hi)⟩
  · constructor
    · intro hi
      by_contra hn
      exact h.2 (crossing_visits_right e f hi hn h20 h21)
    · intro hi
      by_contra hn
      exact h.1 (crossing_visits_left e f hi hn h10 h11)

theorem edge_arc_side (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    (e : Event n) (he : e ∈ events) {i j : Fin n} (hij : EventEdge events i j)
    (hi0 : i ≠ e.1) (hi1 : i ≠ e.2) (hj0 : j ≠ e.1) (hj1 : j ≠ e.2) :
    Inside e i ↔ Inside e j := by
  obtain ⟨f,hf,h⟩ := hij
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact event_arc_side events hsep he hf hi0 hi1 hj0 hj1
  · exact (event_arc_side events hsep he hf hj0 hj1 hi0 hi1).symm

theorem component_inside_arc (events : List (Event n)) (hsep : events.Pairwise LaterOutside)
    (e : Event n) (he : e ∈ events) (root : Fin n) (hroot : Inside e root)
    (havoid : ¬EventReaches events root e.1 ∧ ¬EventReaches events root e.2)
    {j : Fin n} (hp : EventReaches events root j) : Inside e j := by
  induction hp with
  | refl => exact hroot
  | @tail i j hp hij ih =>
    have hi0 : i ≠ e.1 := fun h => havoid.1 (h ▸ hp)
    have hi1 : i ≠ e.2 := fun h => havoid.2 (h ▸ hp)
    have hj0 : j ≠ e.1 := fun h => havoid.1 (h ▸ hp.tail hij)
    have hj1 : j ≠ e.2 := fun h => havoid.2 (h ▸ hp.tail hij)
    exact (edge_arc_side events hsep e he hij hi0 hi1 hj0 hj1).mp ih

#print axioms event_arc_side
#print axioms component_inside_arc
end LX.Core.ZeroGap
