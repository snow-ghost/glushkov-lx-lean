import LRX.ZeroGapTravelCoverage
import LRX.ZeroGapArcSeparation

namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open BufferProgram
variable {n : ℕ} [NeZero n]

theorem event_touches_inside {e : Event n} {b : Fin n} (ht : EventTouches e b)
    (h0 : b ≠ e.1) (h1 : b ≠ e.2) : Inside e b := by
  have hm : Int.ModEq (n : ℤ) ((b : ℤ)-(e.1 : ℤ))
      ((distance e.1 b : ℤ)-0) := by
    simpa using (distance_modEq e.1 b).symm.sub_right (e.1 : ℤ)
  have ht' : Touches (n : ℤ) 0 (distance e.1 e.2 : ℤ) (distance e.1 b : ℤ) :=
    touches_of_modEq hm ht
  obtain ⟨k,hl,hh⟩ := ht'
  have hD : (distance e.1 b : ℤ) < (n : ℤ) := by exact_mod_cast (b-e.1).isLt
  have hE : (distance e.1 e.2 : ℤ) < (n : ℤ) := by exact_mod_cast (e.2-e.1).isLt
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hk : k=0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hk | hk
    · have hk' : k ≤ -1 := by omega
      have hprod : k*(n : ℤ) ≤ -(n : ℤ) := by nlinarith
      simp only [zero_add,min_eq_left (Int.natCast_nonneg _)] at hl
      omega
    · have hk' : 1 ≤ k := by omega
      have hprod : (n : ℤ) ≤ k*(n : ℤ) := by nlinarith
      simp only [zero_add,max_eq_right (Int.natCast_nonneg _)] at hh
      omega
  have hlo := distance_pos e.1 b h0
  have hne : distance e.1 b ≠ distance e.1 e.2 := fun h => h1 (distance_right_injective e.1 h)
  simp only [hk,zero_mul,add_zero,zero_add,max_eq_right (Int.natCast_nonneg _)] at hh
  exact ⟨hlo,by omega⟩

theorem Travel.touched_other_component {events : List (Event n)}
    (hsep : events.Pairwise LaterOutside) {i j b : Fin n} {z : ℤ}
    (hp : Travel events i j z) (ht : Touches (n : ℤ) (i : ℤ) z (b : ℤ))
    (hother : ¬EventReaches events i b) :
    ∃ e ∈ events, EventReaches events i e.1 ∧
      ∀ x, EventReaches events b x → Inside e x := by
  rcases hp.covers ht with h | ⟨e,he,hr,het⟩
  · subst b
    exact False.elim (hother Relation.ReflTransGen.refl)
  · have hsecond : EventReaches events e.1 e.2 :=
      Relation.ReflTransGen.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
    have hb0 : b ≠ e.1 := fun h => hother (h ▸ hr)
    have hb1 : b ≠ e.2 := fun h => hother (h ▸ hr.trans hsecond)
    have havoid : ¬EventReaches events b e.1 ∧ ¬EventReaches events b e.2 := by
      constructor
      · exact fun h => hother (hr.trans (event_reaches_symm events h))
      · exact fun h => hother ((hr.trans hsecond).trans (event_reaches_symm events h))
    exact ⟨e,he,hr,fun x hx => component_inside_arc events hsep e he b
      (event_touches_inside het hb0 hb1) havoid hx⟩

#print axioms event_touches_inside
#print axioms Travel.touched_other_component
end LRX.ZeroGap
