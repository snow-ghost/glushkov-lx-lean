import LRX.FiniteReversalBounds

namespace LRX.FiniteWindow
open FiniteCuts
variable {n b : ℕ}

theorem half_load_before_window (W : Window n b) (f : State b) (e : ℕ)
    (he : e < W.offset) : halfLoad (permutation W f) e=0 := by
  have hf : forward (permutation W f) e=∅ := by
    ext i
    simp only [mem_forward,Finset.notMem_empty,iff_false,not_and]
    intro hi
    have hout : ¬Contains W i := by unfold Contains; omega
    rw [permutation_outside W f i hout]
    omega
  simp [halfLoad,hf]

theorem window_half_load_le_reversal (W : Window n b) (f : State b) (e : ℕ) :
    halfLoad (permutation W f) e ≤ halfLoad (permutation W Fin.revPerm) e := by
  by_cases he : W.offset ≤ e
  · have heq : e=W.offset+(e-W.offset) := by omega
    rw [heq,half_load_window,half_load_window]
    exact half_load_le_reversal f _
  · rw [half_load_before_window W f e (by omega)]
    exact Nat.zero_le _

/-- Reversing a real invariant filling never reduces any cut load. -/
theorem replace_reversal_half_load_mono (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (e : ℕ) :
    halfLoad p e ≤ halfLoad (replace W p f Fin.revPerm) e := by
  have hf := half_load_mul (outsideFactor W p f) (permutation W f) e
    (outside_factor_disjoint W p f f hmatch)
  rw [outside_factor_recover] at hf
  have hg := half_load_mul (outsideFactor W p f) (permutation W Fin.revPerm) e
    (outside_factor_disjoint W p f Fin.revPerm hmatch)
  change halfLoad (replace W p f Fin.revPerm) e=_ at hg
  rw [hf,hg]
  exact Nat.add_le_add_left (window_half_load_le_reversal W f e) _

#print axioms replace_reversal_half_load_mono
end LRX.FiniteWindow
