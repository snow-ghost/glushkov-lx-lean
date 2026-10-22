import LRX.FiniteRootRoute
import LRX.FiniteCycleProfile
import LRX.CyclePartSelection

/-! Select exactly the finite cycles with a positive available left peak.
Their total discount equals the full cycle-profile left load. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

noncomputable def availableLeftCycles (p : State b) (y : ℕ) : List (State b) :=
  (factorList p).filter (fun q => decide (0 < leftPeak q y))

theorem available_left_spec (p : State b) (y : ℕ) :
    (∀ q ∈ availableLeftCycles p y, q.IsCycle) ∧
    (availableLeftCycles p y).Pairwise Equiv.Perm.Disjoint ∧
    (∀ q ∈ availableLeftCycles p y, CyclePart.IsPart q p) ∧
    (∀ q ∈ availableLeftCycles p y, 0 < leftPeak q y) := by
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

theorem sum_positive_peaks (l : List (State b)) (y : ℕ) :
    ((l.filter (fun q => decide (0 < leftPeak q y))).map (fun q => (leftPeak q y : ℤ))).sum=
      (l.map (fun q => (leftPeak q y : ℤ))).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases h : 0 < leftPeak q y
    · simp [h,ih]
    · have hz : leftPeak q y=0 := by omega
      simp [h,hz,ih]

theorem available_left_discount (p : State b) (y : ℕ) :
    2*((availableLeftCycles p y).map (fun q => (leftPeak q y : ℤ))).sum=cycleLeftLoad p y := by
  classical
  rw [availableLeftCycles,sum_positive_peaks]
  have h : ((factorList p).map (fun q => (leftPeak q y : ℤ))).sum=
      ∑ q ∈ p.cycleFactorsFinset, (leftPeak q y : ℤ) := by
    simpa [factorList] using
      (List.sum_toFinset (fun q : State b => (leftPeak q y : ℤ)) (Finset.nodup_toList p.cycleFactorsFinset)).symm
  rw [h,Finset.mul_sum]
  rfl

#print axioms available_left_spec
#print axioms available_left_discount
end LRX.FiniteCuts
