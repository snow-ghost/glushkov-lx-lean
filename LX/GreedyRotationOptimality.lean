import LX.AffineRankRotation
import LX.DeadlinePrice

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem compare_head_idempotent (hn : 2 ≤ n) (d : Fin n → ℤ) :
    compareHead (compareHead d)=compareHead d := by
  by_cases hd : d 1+1 < d 0
  · have he : compareHead d=exchange d := by simp [compareHead,hd]
    exact (congrArg compareHead he).trans (compare_exchange_eq hn d)
  · have he : compareHead d=d := by simp [compareHead,hd]
    simp only [he]

/-- The greedy board after t left moves and the available head comparison. -/
def saturatedSweep (d : Fin n → ℤ) (t : ℕ) : Fin n → ℤ := compareHead (sweep d t)

theorem saturated_sweep_succ (d : Fin n → ℤ) (t : ℕ) :
    saturatedSweep d (t+1)=compareHead (rotate (saturatedSweep d t)) := rfl

theorem saturated_sweep_balance (d : Fin n → ℤ) (t : ℕ) :
    (∑ i,saturatedSweep d t i)=∑ i,d i := by
  unfold saturatedSweep compareHead
  split_ifs
  · rw [exchange_sum,sweep_balance]
  · rw [sweep_balance]

/-- Greedy comparisons dominate every literal LX schedule with the same
number of left moves, including skipped or repeated exchanges. -/
theorem saturated_sweep_rank_le_run (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter) :
    RankLE (saturatedSweep d (w.count .l)) (run w d) := by
  induction w using List.reverseRecOn with
  | nil => exact compare_rank_le_self hn d
  | append_singleton w a ih =>
    cases a with
    | x =>
      have hh := rank_le_trans (compare_rank_mono hn ih) (compare_rank_le_exchange hn (run w d))
      have he : compareHead (saturatedSweep d (w.count .l))=saturatedSweep d (w.count .l) :=
        compare_head_idempotent hn _
      rw [he] at hh
      simpa [List.count_append,run_append,run,step] using hh
    | l =>
      have hh := rank_le_trans (compare_rank_mono hn (rotate_rank_mono hn ih))
        (compare_rank_le_self hn (rotate (run w d)))
      simpa [List.count_append,run_append,run,step,saturated_sweep_succ] using hh

theorem saturated_sweep_zero_of_word (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hb : ∑ i,d i=0) (hz : ∀ i,run w d i=0) :
    ∀ i,saturatedSweep d (w.count .l) i=0 := by
  have hr := saturated_sweep_rank_le_run hn d w
  have he : run w d=(fun _ => 0) := funext hz
  rw [he] at hr
  exact zero_of_rank_le_zero _ (by rw [saturated_sweep_balance,hb]) hr

/-- Optimality of the greedy scan's rotation count for a fixed exact lift.
The final phase and the exchange count still need to be charged separately. -/
theorem ScanTrace.rotations_le_any_word (hn : 2 ≤ n) {d : Fin n → ℤ}
    {g : List Letter} (hg : ScanTrace d g) (hb : ∑ i,d i=0)
    (w : List Letter) (hw : ∀ i,run w d i=0) : g.count .l ≤ w.count .l :=
  hg.rotations_le_of_compare_zero hn _ (saturated_sweep_zero_of_word hn d w hb hw)

#print axioms saturated_sweep_rank_le_run
#print axioms ScanTrace.rotations_le_any_word
end LX.AffineScan
