import LRX.EventTrace
import LRX.PairOrder
import Mathlib

/-! A trace without repeated lifted pairs consists precisely of the pair orbits
whose relative order differs between the initial and final configurations. -/
namespace LRX.LiftedModel
variable {n : ℕ} [NeZero n]

theorem before_run_of_absent (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hk : key.Valid)
    (habsent : key ∉ events w s) : key.Before (run w s) ↔ key.Before s := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    have hsa := step_aligned hn a hs
    cases a with
    | l =>
      have h := ih hsa habsent
      simpa only [run, PairKey.Before, step] using h
    | r =>
      have h := ih hsa habsent
      simpa only [run, PairKey.Before, step] using h
    | x =>
      have hnot : key ∉ events w (step .x s) := fun h => habsent (List.mem_cons_of_mem _ h)
      have hne : eventKey s ≠ key := by
        intro h
        exact habsent (by simp [events, h])
      exact (ih hsa hnot).trans (x_changes_only_event hn hs key hk hne)

theorem before_run_of_present (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hk : key.Valid)
    (hnd : (events w s).Nodup) (hmem : key ∈ events w s) :
    key.Before (run w s) ↔ ¬ key.Before s := by
  induction w generalizing s with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons a w ih =>
    have hsa := step_aligned hn a hs
    cases a with
    | l =>
      have h := ih hsa hnd hmem
      simpa only [run, PairKey.Before, step] using h
    | r =>
      have h := ih hsa hnd hmem
      simpa only [run, PairKey.Before, step] using h
    | x =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hmem with he | hm
      · have ha : key ∉ events w (step .x s) := by simpa only [he] using hnot
        exact (before_run_of_absent hn w hsa key hk ha).trans (x_changes_event hn hs key hk he.symm)
      · have hne : eventKey s ≠ key := fun he => hnot (he ▸ hm)
        exact (ih hsa htail hm).trans (not_congr (x_changes_only_event hn hs key hk hne))

theorem event_member_valid (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hmem : key ∈ events w s) : key.Valid := by
  obtain ⟨u, v, _, hk⟩ := (mem_events w s key).mp hmem
  rw [← hk]
  exact event_key_valid hn (run_aligned hn u hs)

theorem reduced_trace_inversions (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (hnd : (events w s).Nodup) (key : PairKey n) :
    key ∈ events w s ↔ key.Valid ∧ ¬ (key.Before s ↔ key.Before (run w s)) := by
  constructor
  · intro hmem
    have hk := event_member_valid hn w hs key hmem
    refine ⟨hk, ?_⟩
    have h := before_run_of_present hn w hs key hk hnd hmem
    tauto
  · rintro ⟨hk, hchange⟩
    by_contra hno
    exact hchange (before_run_of_absent hn w hs key hk hno).symm

#print axioms before_run_of_absent
#print axioms reduced_trace_inversions
end LRX.LiftedModel
