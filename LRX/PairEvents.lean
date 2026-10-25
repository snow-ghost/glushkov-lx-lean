import LRX.LiftedPair
import Mathlib

/-! Canonical keys of lifted pair events. The stored shift is n times the copy
index, avoiding any loss through integer division. Order reversal negates it. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing

structure PairKey (n : ℕ) where
  first : Fin n
  second : Fin n
  shift : ℤ
  deriving DecidableEq

variable {n : ℕ} [NeZero n]

def normalizePair (a b : Fin n) (shift : ℤ) : PairKey n :=
  if a ≤ b then ⟨a,b,shift⟩ else ⟨b,a,-shift⟩

def PairKey.action (key : PairKey n) : Configuration n → Configuration n :=
  pairRename key.first key.second key.shift

def eventKey (s : Configuration n) : PairKey n :=
  let a := s.physical.tokens s.physical.cursor
  let b := s.physical.tokens (s.physical.cursor+1)
  normalizePair a b (s.position a+1-s.position b)

omit [NeZero n] in
theorem normalize_pair_action (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    (normalizePair a b shift).action=pairRename a b shift := by
  unfold normalizePair
  split_ifs
  · rfl
  · exact pair_rename_reverse a b shift hab

omit [NeZero n] in
theorem normalize_pair_distinct (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    (normalizePair a b shift).first ≠ (normalizePair a b shift).second := by
  unfold normalizePair
  split_ifs <;> first | exact hab | exact Ne.symm hab

theorem event_pair_distinct (hn : 2 ≤ n) (s : Configuration n) :
    (eventKey s).first ≠ (eventKey s).second := by
  apply normalize_pair_distinct
  intro h
  exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)

theorem x_event_action (hn : 2 ≤ n) (s : Configuration n) :
    step .x s=(eventKey s).action s := by
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  rw [eventKey, normalize_pair_action _ _ _ hne]
  exact x_as_pair_rename s _ _ hne rfl rfl

theorem event_shift_dvd {s : Configuration n} (hs : Aligned s) :
    (n : ℤ) ∣ (eventKey s).shift := by
  have h := pair_offset_dvd hs _ _ rfl rfl
  dsimp only [eventKey, normalizePair]
  split_ifs
  · exact h
  · exact dvd_neg.mpr h

/-- Two equal canonical keys can be deleted even with an arbitrary middle word;
integer token positions, finite permutation and integer cursor all agree. -/
theorem delete_equal_events (hn : 2 ≤ n) (middle : List Letter) (s : Configuration n)
    (he : eventKey s=eventKey (run middle (step .x s))) :
    run ([.x]++middle++[.x]) s=run middle s := by
  let key := eventKey s
  have hne : key.first ≠ key.second := event_pair_distinct hn s
  apply delete_renamed_pair (Equiv.swap key.first key.second)
    (pairOffset key.first key.second key.shift)
    (Equiv.swap_apply_self _ _) (pair_offset_cancel _ _ _ hne)
  · exact x_event_action hn s
  · have h := x_event_action hn (run middle (step .x s))
    rw [← he] at h
    exact h

theorem delete_equal_events_context (hn : 2 ≤ n) (u middle v : List Letter)
    (s : Configuration n)
    (he : eventKey (run u s)=eventKey (run middle (step .x (run u s)))) :
    run (u++[.x]++middle++[.x]++v) s=run (u++middle++v) s := by
  have h := delete_equal_events hn middle (run u s) he
  simpa only [run_append, run] using congrArg (run v) h

#print axioms event_shift_dvd
#print axioms delete_equal_events_context
end LRX.LiftedModel
