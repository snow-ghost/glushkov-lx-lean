import LX.ForwardCarrier

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Periodic target values, read in the current cursor coordinates. -/
def atTarget (d : Fin n → ℤ) (j : ℕ) : ℤ := (j : ℤ) + d (j : Fin n)

def compareHead (d : Fin n → ℤ) : Fin n → ℤ :=
  if d 1 + 1 < d 0 then exchange d else d

def sweepStep (d : Fin n → ℤ) : Fin n → ℤ := rotate (compareHead d)

def sweep (d : Fin n → ℤ) : ℕ → (Fin n → ℤ)
  | 0 => d
  | k+1 => sweepStep (sweep d k)

def sweepStepWord (d : Fin n → ℤ) : List Letter :=
  if d 1 + 1 < d 0 then [.x, .l] else [.l]

def sweepWord (d : Fin n → ℤ) : ℕ → List Letter
  | 0 => []
  | k+1 => sweepWord d k ++ sweepStepWord (sweep d k)

theorem run_sweep_step (d : Fin n → ℤ) : run (sweepStepWord d) d = sweepStep d := by
  unfold sweepStepWord sweepStep compareHead
  split_ifs <;> rfl

theorem run_sweep_word (d : Fin n → ℤ) (k : ℕ) : run (sweepWord d k) d = sweep d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweepWord, run_append, ih, run_sweep_step, sweep]

theorem sweep_word_rotations (d : Fin n → ℤ) (k : ℕ) : (sweepWord d k).count .l = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sweepWord, List.count_append, ih, sweepStepWord]
    split_ifs <;> simp

theorem at_rotate (d : Fin n → ℤ) (j : ℕ) :
    atTarget (rotate d) j = atTarget d (j+1) - 1 := by
  simp only [atTarget, rotate, finRotate_apply, Nat.cast_add, Nat.cast_one]
  omega

theorem at_period (d : Fin n → ℤ) : atTarget d n = atTarget d 0 + n := by
  simp [atTarget, add_comm]

theorem compare_head_zero (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 0 = min (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_left, h01, ite_true, ite_false, sub_zero]
    rw [min_eq_right (by omega)]
    omega
  · exact (min_eq_left (by omega)).symm

theorem compare_head_one (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (compareHead d) 1 = max (atTarget d 0) (atTarget d 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  simp only [compareHead, atTarget, Nat.cast_zero, Nat.cast_one, zero_add]
  split_ifs with h
  · simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false, add_zero]
    rw [max_eq_left (by omega)]
    omega
  · exact (max_eq_right (by omega)).symm

theorem compare_head_tail (d : Fin n → ℤ) (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    atTarget (compareHead d) j = atTarget d j := by
  have hj0 : (j : Fin n) ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn] at hh
    omega
  have hj1 : (j : Fin n) ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hjn, Nat.mod_eq_of_lt (by omega : 1 < n)] at hh
    omega
  unfold compareHead
  split_ifs
  · simp [atTarget, exchange, Equiv.swap_apply_of_ne_of_ne hj0 hj1, hj0, hj1]
  · rfl

theorem sweep_step_head (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (sweepStep d) 0 = max (atTarget d 0) (atTarget d 1) - 1 := by
  rw [sweepStep, at_rotate, compare_head_one hn]

theorem sweep_step_last (hn : 2 ≤ n) (d : Fin n → ℤ) :
    atTarget (sweepStep d) (n-1) = min (atTarget d 0) (atTarget d 1) + n - 1 := by
  rw [sweepStep, at_rotate, Nat.sub_add_cancel (by omega : 1 ≤ n), at_period, compare_head_zero hn]

/-- A prefix of the actual LX program has the ordinary forward carrier and untouched future entries. -/
theorem sweep_prefix_values (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ) (hk : k < n) :
    atTarget (sweep d k) 0 = ForwardCarrier.sweepPrefix (atTarget d) k k - k ∧
    ∀ j : ℕ, 0 < j → j+k < n →
      atTarget (sweep d k) j = atTarget d (j+k) - k := by
  induction k with
  | zero => simp [sweep, ForwardCarrier.sweepPrefix]
  | succ k ih =>
    obtain ⟨hhead, htail⟩ := ih (by omega)
    constructor
    · rw [sweep, sweep_step_head hn, hhead, htail 1 (by omega) (by omega),
        ForwardCarrier.carrier_step]
      have he : 1+k=k+1 := by omega
      rw [he]
      push_cast
      by_cases h : ForwardCarrier.sweepPrefix (atTarget d) k k ≤ atTarget d (k+1)
      · rw [max_eq_right h, max_eq_right (by omega)]
        omega
      · rw [max_eq_left (by omega : atTarget d (k+1) ≤ ForwardCarrier.sweepPrefix (atTarget d) k k),
          max_eq_left (by omega)]
        omega
    · intro j hj hjk
      rw [sweep, sweepStep, at_rotate, compare_head_tail _ (j+1) (by omega) (by omega),
        htail (j+1) (by omega) (by omega)]
      have he : j+1+k=j+(k+1) := by omega
      rw [he]
      push_cast
      omega

/-- The maximum formula now refers to a literal word over L and X. -/
theorem sweep_word_carrier_le_iff (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ)
    (hk : k < n) (x : ℤ) :
    atTarget (run (sweepWord d k) d) 0 + k ≤ x ↔
      ∀ j ≤ k, atTarget d j ≤ x := by
  rw [run_sweep_word, (sweep_prefix_values hn d k hk).1, sub_add_cancel]
  exact ForwardCarrier.carrier_le_iff _ k x

/-- The first output cell is untouched again until the scan returns to the seam. -/
theorem sweep_first_output (hn : 2 ≤ n) (d : Fin n → ℤ) (k : ℕ)
    (hk0 : 1 ≤ k) (hkn : k < n) :
    atTarget (sweep d k) (n-k) = min (atTarget d 0) (atTarget d 1) + n - k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      simpa only [Nat.zero_add, sweep, Nat.cast_one] using sweep_step_last hn d
    · rw [sweep, sweepStep, at_rotate]
      have he : n-(k+1)+1=n-k := by omega
      rw [he, compare_head_tail _ (n-k) (by omega) (by omega), ih (by omega) (by omega)]
      push_cast
      omega

/-- After a backward exchange the token is revisited after exactly n-1 rotations.
At that visit it moves backwards again precisely when a larger target remains in the preceding period. -/
theorem backward_return_descent (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hhead : atTarget d 0 ≤ atTarget d 1) :
    (sweep d (n-1)) 1 + 1 < (sweep d (n-1)) 0 ↔
      ∃ j : ℕ, j < n ∧ atTarget d 0 + n < atTarget d j := by
  have hfirst := sweep_first_output hn d (n-1) (by omega) (by omega)
  have he : n-(n-1)=1 := by omega
  rw [he, min_eq_left hhead] at hfirst
  have hcarrier := (sweep_prefix_values hn d (n-1) (by omega)).1
  have hread0 (e : Fin n → ℤ) : atTarget e 0 = e 0 := by simp [atTarget]
  have hread1 (e : Fin n → ℤ) : atTarget e 1 = 1+e 1 := by simp [atTarget]
  have hsub : ((n-1 : ℕ) : ℤ) = (n : ℤ)-1 := by omega
  have hh : (sweep d (n-1)) 1 + 1 < (sweep d (n-1)) 0 ↔
      atTarget d 0 + n < ForwardCarrier.sweepPrefix (atTarget d) (n-1) (n-1) := by
    rw [hread0] at hcarrier
    rw [hread1] at hfirst
    omega
  rw [hh, ForwardCarrier.lt_carrier_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by omega, h⟩

/-- A real descent exchange leaves the head sorted, as required by the return lemma. -/
theorem exchanged_head_sorted (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1+1 < d 0) : atTarget (exchange d) 0 ≤ atTarget (exchange d) 1 := by
  have h0 := compare_head_zero hn d
  have h1 := compare_head_one hn d
  simp only [compareHead, ite_eq_left hdesc] at h0 h1
  rw [h0, h1]
  exact min_le_max

theorem sweep_succ_start (d : Fin n → ℤ) (k : ℕ) :
    sweep d (k+1) = sweep (sweepStep d) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg sweepStep ih

/-- Once the bounded comparison schedule has sorted, the genuine stopping trace
has used no more than the scheduled number of rotations. -/
theorem ScanTrace.rotations_le_of_compare_zero (hn : 2 ≤ n) {d : Fin n → ℤ}
    {w : List Letter} (ht : ScanTrace d w) (k : ℕ)
    (hz : ∀ i, compareHead (sweep d k) i = 0) : w.count .l ≤ k := by
  induction k generalizing d w with
  | zero =>
    cases ht with
    | done => simp
    | @left d w hnon hle tail =>
      have he : compareHead (sweep d 0) = d := by
        simp [sweep, compareHead, not_lt.mpr hle]
      rw [he] at hz
      exact False.elim (hnon hz)
    | @swap d w hdesc tail =>
      have he : compareHead (sweep d 0) = exchange d := by
        simp [sweep, compareHead, hdesc]
      rw [he] at hz
      have hw : w=[] := tail.unique (ScanTrace.done hz)
      simp [hw]
  | succ k ih =>
    rw [sweep_succ_start] at hz
    cases ht with
    | done => simp
    | @left d w hnon hle tail =>
      have he : sweepStep d = rotate d := by simp [sweepStep, compareHead, not_lt.mpr hle]
      rw [he] at hz
      have hh := ih tail hz
      simpa only [List.count_cons_self] using Nat.add_le_add_right hh 1
    | @swap d w hdesc tail =>
      have he : sweepStep d = rotate (exchange d) := by simp [sweepStep, compareHead, hdesc]
      rw [he] at hz
      cases tail with
      | done => simp
      | left _ _ tail' =>
        have hh := ih tail' hz
        simpa using Nat.add_le_add_right hh 1
      | swap hdesc' _ =>
        have hh := exchanged_head_sorted hn d hdesc
        simp only [atTarget, Nat.cast_zero, Nat.cast_one, zero_add] at hh
        omega

#print axioms run_sweep_word
#print axioms sweep_prefix_values
#print axioms sweep_word_carrier_le_iff
#print axioms backward_return_descent
#print axioms ScanTrace.rotations_le_of_compare_zero
end LX.AffineScan
