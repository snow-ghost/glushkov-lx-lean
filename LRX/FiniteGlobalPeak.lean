import LRX.GlobalPeakServiceFamily

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem moved_global_peak_positive (p : State n) (i : Fin n) (hi : p i ≠ i) :
    0 < leftPeak p n := by
  have hne : (p i).val ≠ i.val := fun h => hi (Fin.ext h)
  obtain ⟨e,he,hpos⟩ : ∃ e ≤ n, 0 < halfLoad p e := by
    by_cases hh : i.val < (p i).val
    · refine ⟨i.val+1,by have := i.isLt; omega,?_⟩
      exact Finset.card_pos.mpr ⟨i,(mem_forward p _ i).mpr ⟨by omega,by omega⟩⟩
    · refine ⟨(p i).val+1,by have := (p i).isLt; omega,?_⟩
      unfold halfLoad
      rw [cut_balance]
      exact Finset.card_pos.mpr ⟨i,(mem_backward p _ i).mpr ⟨by omega,by omega⟩⟩
  have hb : halfLoad p e ≤ leftPeak p n := Finset.le_sup (Finset.mem_range.mpr (by omega))
  omega

#print axioms moved_global_peak_positive
end LRX.FiniteCuts
