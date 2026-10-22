import LRX.FiniteRootRoute
import LRX.FiniteCycleProfile
import LRX.CyclePartSelection

/-! Select exactly the finite cycles with a positive available right peak.
Their total discount equals the full cycle-profile right load. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

noncomputable def availableRightCycles (p : State b) (y : ℕ) : List (State b) :=
  (factorList p).filter (fun q => decide (0 < rightPeak q y))

theorem available_right_spec (p : State b) (y : ℕ) :
    (∀ q ∈ availableRightCycles p y, q.IsCycle) ∧
    (availableRightCycles p y).Pairwise Equiv.Perm.Disjoint ∧
    (∀ q ∈ availableRightCycles p y, CyclePart.IsPart q p) ∧
    (∀ q ∈ availableRightCycles p y, 0 < rightPeak q y) := by
  obtain ⟨hc,hd,hp⟩ := factor_list_spec p
  refine ⟨?_,hd.filter _,?_,?_⟩
  · intro q hq
    exact hc q (List.mem_filter.mp hq).1
  · intro q hq
    apply CyclePart.cycle_factor
    have hm := (List.mem_filter.mp hq).1
    simpa [factorList] using hm
  · intro q hq
    exact of_decide_eq_true (List.mem_filter.mp hq).2

theorem sum_positive_right_peaks (l : List (State b)) (y : ℕ) :
    ((l.filter (fun q => decide (0 < rightPeak q y))).map (fun q => (rightPeak q y : ℤ))).sum=
      (l.map (fun q => (rightPeak q y : ℤ))).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases h : 0 < rightPeak q y
    · simp [h,ih]
    · have hz : rightPeak q y=0 := by omega
      simp [h,hz,ih]

theorem available_right_discount (p : State b) (y : ℕ) :
    2*((availableRightCycles p y).map (fun q => (rightPeak q y : ℤ))).sum=cycleRightLoad p y := by
  classical
  rw [availableRightCycles,sum_positive_right_peaks]
  have h : ((factorList p).map (fun q => (rightPeak q y : ℤ))).sum=
      ∑ q ∈ p.cycleFactorsFinset, (rightPeak q y : ℤ) := by
    simpa [factorList] using
      (List.sum_toFinset (fun q : State b => (rightPeak q y : ℤ)) (Finset.nodup_toList p.cycleFactorsFinset)).symm
  rw [h,Finset.mul_sum]
  rfl

#print axioms available_right_spec
#print axioms available_right_discount
end LRX.FiniteCuts
