import LX.BackwardDepth

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def atDepth (d : Fin n → ℤ) (j : ℕ) : ℕ := backwardDepth d (j : Fin n)

theorem at_depth_rotate (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ) :
    atDepth (rotate d) j = atDepth d (j+1) := by
  simp only [atDepth, rotate_backward_depth hn, finRotate_apply, Nat.cast_add, Nat.cast_one]

theorem compare_head_tail_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (j : ℕ)
    (hj : 2 ≤ j) (hjn : j < n) : atDepth (compareHead d) j = atDepth d j := by
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
  · exact exchange_other_depth hn d (j : Fin n) hj0 hj1
  · rfl

theorem compare_sorted_head (d : Fin n → ℤ) (hhead : atTarget d 0 ≤ atTarget d 1) :
    compareHead d = d := by
  have hle : d 0 ≤ d 1+1 := by simpa [atTarget, add_comm] using hhead
  simp only [compareHead, ite_eq_right (not_lt.mpr hle)]

/-- While the token crosses the cursor seam, comparisons of other tokens do not alter its depth. -/
theorem sweep_first_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hhead : atTarget d 0 ≤ atTarget d 1) (k : ℕ) (hk0 : 1 ≤ k) (hkn : k < n) :
    atDepth (sweep d k) (n-k) = backwardDepth d 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      simp only [Nat.zero_add, sweep, sweepStep, at_depth_rotate hn]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), compare_sorted_head d hhead]
      simp [atDepth]
    · rw [sweep, sweepStep, at_depth_rotate hn]
      have he : n-(k+1)+1=n-k := by omega
      rw [he, compare_head_tail_depth hn _ (n-k) (by omega) (by omega)]
      exact ih (by omega) (by omega)

/-- A nonzero depth forces another backward exchange on the next visit. -/
theorem return_descent_of_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hhead : atTarget d 0 ≤ atTarget d 1)
    (hb : 0 < backwardDepth d 0) :
    (sweep d (n-1)) 1 + 1 < (sweep d (n-1)) 0 := by
  apply (backward_return_descent hn d hhead).mpr
  obtain ⟨j,hj⟩ := (backward_depth_head_pos_iff d hi).mp hb
  refine ⟨j.val, j.isLt, ?_⟩
  simpa [atTarget, targets] using hj

/-- Exactly one predecessor is consumed at each subsequent visit, spaced by n-1 rotations. -/
theorem backward_return_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hhead : atTarget d 0 ≤ atTarget d 1)
    (hb : 0 < backwardDepth d 0) :
    backwardDepth (exchange (sweep d (n-1))) 0 + 1 = backwardDepth d 0 := by
  have hd := return_descent_of_depth hn d hi hhead hb
  have hstay := sweep_first_depth hn d hhead (n-1) (by omega) (by omega)
  have he : n-(n-1)=1 := by omega
  rw [he] at hstay
  change backwardDepth (sweep d (n-1)) 1 = backwardDepth d 0 at hstay
  exact (exchange_backward_depth hn (sweep d (n-1)) hd).trans hstay

def returnWord (d : Fin n → ℤ) : List Letter := sweepWord d (n-1) ++ [.x]

theorem run_return_word (d : Fin n → ℤ) :
    run (returnWord d) d = exchange (sweep d (n-1)) := by
  rw [returnWord, run_append, run_sweep_word]
  rfl

theorem return_word_rotations (d : Fin n → ℤ) : (returnWord d).count .l = n-1 := by
  simp [returnWord, sweep_word_rotations]

#print axioms sweep_first_depth
#print axioms backward_return_depth
#print axioms run_return_word
#print axioms return_word_rotations
end LX.AffineScan
