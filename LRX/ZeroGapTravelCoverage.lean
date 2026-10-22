import LRX.ZeroGapEventGraph
import LRX.PeriodicTouches

/-! Integer motion along events covers every periodically touched vertex of
its total displacement, within the same event component. -/
namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open BufferProgram
variable {n : ℕ} [NeZero n]

theorem touches_split (N a x y b : ℤ) (h : Touches N a (x+y) b) :
    Touches N a x b ∨ Touches N (a+x) y b := by
  obtain ⟨k,hl,hh⟩ := h
  by_cases hfirst : min a (a+x) ≤ b+k*N ∧ b+k*N ≤ max a (a+x)
  · exact Or.inl ⟨k,hfirst⟩
  · right
    refine ⟨k,?_,?_⟩ <;> omega

theorem distance_modEq (i j : Fin n) :
    Int.ModEq (n : ℤ) ((i : ℤ)+(distance i j : ℤ)) (j : ℤ) := by
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  simp [distance]

theorem event_move_modEq {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : EventMove events i j z) : Int.ModEq (n : ℤ) ((i : ℤ)+z) (j : ℤ) := by
  obtain ⟨e,he,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact distance_modEq _ _
  · have h := (distance_modEq e.1 e.2).symm.add_right (-(distance e.1 e.2 : ℤ))
    simpa using h

theorem event_move_edge {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : EventMove events i j z) : EventEdge events i j := by
  obtain ⟨e,he,h⟩ := h
  exact ⟨e,he,h.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩)⟩

def EventTouches (e : Event n) (b : Fin n) : Prop :=
  Touches (n : ℤ) (e.1 : ℤ) (distance e.1 e.2 : ℤ) (b : ℤ)

theorem event_move_touches {events : List (Event n)} {i j b : Fin n} {z : ℤ}
    (h : EventMove events i j z) (ht : Touches (n : ℤ) (i : ℤ) z (b : ℤ)) :
    ∃ e ∈ events, EventReaches events i e.1 ∧ EventTouches e b := by
  obtain ⟨e,he,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨e,he,Relation.ReflTransGen.refl,ht⟩
  · refine ⟨e,he,Relation.ReflTransGen.single ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩,?_⟩
    have hm : Int.ModEq (n : ℤ) ((b : ℤ)-(e.2 : ℤ))
        ((b : ℤ)-((e.1 : ℤ)+(distance e.1 e.2 : ℤ))) :=
      (distance_modEq e.1 e.2).symm.sub_left _
    have ht' := touches_of_modEq hm ht
    obtain ⟨k,hl,hh⟩ := ht'
    refine ⟨k,?_,?_⟩ <;> omega

theorem Travel.covers {events : List (Event n)} {i j b : Fin n} {z : ℤ}
    (hp : Travel events i j z) (ht : Touches (n : ℤ) (i : ℤ) z (b : ℤ)) :
    b=i ∨ ∃ e ∈ events, EventReaches events i e.1 ∧ EventTouches e b := by
  induction hp with
  | refl i =>
    left
    obtain ⟨k,hl,hh⟩ := ht
    have he : (b : ℤ)+k*(n : ℤ)=(i : ℤ) := by omega
    have hm : Int.ModEq (n : ℤ) (b : ℤ) (i : ℤ) := by
      rw [← he]
      exact Int.modEq_iff_dvd.mpr ⟨k,by ring⟩
    exact Fin.ext (by have h := (LiftedModel.cast_eq_iff_modEq _ _).mpr hm; simpa using congrArg Fin.val h)
  | @head i j k a c he hp ih =>
    rcases touches_split _ _ _ _ _ ht with ht | ht
    · exact Or.inr (event_move_touches he ht)
    · have hm : Int.ModEq (n : ℤ) ((b : ℤ)-((i : ℤ)+a)) ((b : ℤ)-(j : ℤ)) :=
        (event_move_modEq he).sub_left _
      rcases ih (touches_of_modEq hm ht) with hb | ⟨e,hem,hr,het⟩
      · subst b
        have hj : Touches (n : ℤ) (i : ℤ) a (j : ℤ) := by
          have hm' := (event_move_modEq he).sub_right (i : ℤ)
          apply touches_of_modEq hm'
          exact ⟨0,by simp,by simp⟩
        exact Or.inr (event_move_touches he hj)
      · exact Or.inr ⟨e,hem,(Relation.ReflTransGen.single (event_move_edge he)).trans hr,het⟩

#print axioms Travel.covers
end LRX.ZeroGap
