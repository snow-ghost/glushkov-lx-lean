import LX.PairEvents
import Mathlib

/-! Exact event traces and detection of repeated lifted pairs in a literal word. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

def events : List Letter → Configuration n → List (PairKey n)
  | [], _ => []
  | .x::w, s => eventKey s :: events w (step .x s)
  | .l::w, s => events w (step .l s)
  | .r::w, s => events w (step .r s)

theorem events_append (u v : List Letter) (s : Configuration n) :
    events (u++v) s=events u s ++ events v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => cases a <;> simp only [List.cons_append, events, run, ih, List.cons_append]

theorem mem_events (w : List Letter) (s : Configuration n) (key : PairKey n) :
    key ∈ events w s ↔ ∃ u v, w=u++[.x]++v ∧ eventKey (run u s)=key := by
  constructor
  · induction w generalizing s with
    | nil => simp [events]
    | cons a w ih =>
      have liftTail (h : key ∈ events w (step a s)) :
          ∃ u v, a::w=u++[.x]++v ∧ eventKey (run u s)=key := by
        obtain ⟨u, v, he, hk⟩ := ih _ h
        exact ⟨a::u, v, by simp only [List.cons_append, he], hk⟩
      cases a with
      | l => exact liftTail
      | r => exact liftTail
      | x =>
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨[], w, rfl, h.symm⟩
        · exact liftTail h
  · rintro ⟨u, v, rfl, hk⟩
    simp [events_append, events, hk]

def RepeatedEvents (w : List Letter) (s : Configuration n) : Prop :=
  ∃ u middle v, w=u++[.x]++middle++[.x]++v ∧
    eventKey (run u s)=eventKey (run middle (step .x (run u s)))

theorem repeated_of_not_nodup (w : List Letter) (s : Configuration n)
    (h : ¬ (events w s).Nodup) : RepeatedEvents w s := by
  induction w generalizing s with
  | nil => exact False.elim (h (by simp [events]))
  | cons a w ih =>
    have liftTail (ht : ¬ (events w (step a s)).Nodup) : RepeatedEvents (a::w) s := by
      obtain ⟨u, middle, v, he, hk⟩ := ih _ ht
      exact ⟨a::u, middle, v, by simp only [List.cons_append, he], hk⟩
    cases a with
    | l => exact liftTail h
    | r => exact liftTail h
    | x =>
      have hh : eventKey s ∈ events w (step .x s) ∨ ¬ (events w (step .x s)).Nodup := by
        simpa only [events, List.nodup_cons, not_and_or, not_not] using h
      rcases hh with hh | hh
      · obtain ⟨middle, v, he, hk⟩ := (mem_events w (step .x s) (eventKey s)).mp hh
        exact ⟨[], middle, v, by simp only [List.nil_append, List.cons_append, he], hk.symm⟩
      · exact liftTail hh

#print axioms mem_events
#print axioms repeated_of_not_nodup
end LX.Core.LiftedModel
