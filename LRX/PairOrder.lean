import LRX.PairEvents
import Mathlib

/-! Relative order of periodic token copies. A physical X changes the order of
exactly its own lifted pair orbit. This links reduced traces to inversions. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def PairKey.Before (key : PairKey n) (s : Configuration n) : Prop :=
  s.position key.first < s.position key.second+key.shift

def PairKey.Valid (key : PairKey n) : Prop :=
  key.first < key.second ∧ (n : ℤ) ∣ key.shift

theorem positions_ne_periodic {s : Configuration n} (hs : Aligned s)
    (a b : Fin n) (hab : a ≠ b) (shift : ℤ) (hdiv : (n : ℤ) ∣ shift) :
    s.position a ≠ s.position b+shift := by
  intro he
  have hz : (shift : Fin n)=0 := by
    have h := AffineLift.cast_eq_of_modEq (Int.modEq_zero_iff_dvd.mpr hdiv)
    simpa using h
  have hc : (s.position a : Fin n)=(s.position b : Fin n) := by
    rw [he, Int.cast_add, hz, add_zero]
  rw [hs.2 a, hs.2 b] at hc
  exact hab (s.physical.tokens.symm.injective hc)

omit [NeZero n] in
theorem pair_action_order {key : PairKey n} {s : Configuration n}
    (hne : key.first ≠ key.second)
    (hpos : s.position key.first ≠ s.position key.second+key.shift) :
    key.Before (key.action s) ↔ ¬ key.Before s := by
  simp only [PairKey.Before, PairKey.action, pairRename, rename,
    Equiv.swap_apply_left, Equiv.swap_apply_right, pairOffset,
    ite_true, ite_eq_right (Ne.symm hne)]
  omega

theorem x_changes_only_event (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s)
    (key : PairKey n) (hk : key.Valid) (hne : eventKey s ≠ key) :
    key.Before (step .x s) ↔ key.Before s := by
  have hab : key.first ≠ key.second := ne_of_lt hk.1
  have hpre := positions_ne_periodic hs key.first key.second hab key.shift hk.2
  have hpost := positions_ne_periodic (step_aligned hn .x hs)
    key.first key.second hab key.shift hk.2
  let a := s.physical.tokens s.physical.cursor
  let b := s.physical.tokens (s.physical.cursor+1)
  have hdist : a ≠ b := fun h => neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  by_contra hchange
  have horient :
      (key.first=a ∧ key.second=b ∧ key.shift=s.position a+1-s.position b) ∨
      (key.first=b ∧ key.second=a ∧ key.shift=-(s.position a+1-s.position b)) := by
    change ¬ ((s.position key.first+(if key.first=a then 1 else 0)-
      (if key.first=b then 1 else 0) <
      s.position key.second+(if key.second=a then 1 else 0)-
      (if key.second=b then 1 else 0)+key.shift) ↔
      s.position key.first < s.position key.second+key.shift) at hchange
    change s.position key.first+(if key.first=a then 1 else 0)-
      (if key.first=b then 1 else 0) ≠
      s.position key.second+(if key.second=a then 1 else 0)-
      (if key.second=b then 1 else 0)+key.shift at hpost
    by_cases hfa : key.first=a <;> by_cases hfb : key.first=b <;>
      by_cases hsa : key.second=a <;> by_cases hsb : key.second=b <;>
      simp_all <;> omega
  apply hne
  rcases horient with ⟨hfa, hsb, hz⟩ | ⟨hfb, hsa, hz⟩
  · have hnorm : normalizePair key.first key.second key.shift=key := by
      cases key
      simp only [normalizePair, ite_eq_left (le_of_lt hk.1)]
    simpa only [eventKey, a, b, hfa, hsb, hz] using hnorm
  · have hnorm : normalizePair key.second key.first (-key.shift)=key := by
      cases key
      simp only [normalizePair, ite_eq_right (not_le.mpr hk.1), neg_neg]
    simpa only [eventKey, a, b, hfb, hsa, hz, neg_neg] using hnorm

theorem x_changes_event (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s)
    (key : PairKey n) (hk : key.Valid) (he : eventKey s=key) :
    key.Before (step .x s) ↔ ¬ key.Before s := by
  rw [x_event_action hn s, he]
  exact pair_action_order (ne_of_lt hk.1)
    (positions_ne_periodic hs key.first key.second (ne_of_lt hk.1) key.shift hk.2)

theorem event_key_valid (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s) :
    (eventKey s).Valid := by
  refine ⟨?_, event_shift_dvd hs⟩
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  dsimp only [eventKey, normalizePair]
  split_ifs with h
  · exact lt_of_le_of_ne h hne
  · exact lt_of_not_ge h

#print axioms x_changes_only_event
#print axioms x_changes_event
end LRX.LiftedModel
