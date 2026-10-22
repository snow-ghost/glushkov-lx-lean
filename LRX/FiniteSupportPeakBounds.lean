import LRX.FiniteCycleSupportBudget
import LRX.FiniteQuadraticGap

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem twice_half_load_le_support (p : State n) (e : ℕ) : 2*halfLoad p e ≤ p.support.card := by
  classical
  have hdis : Disjoint (forward p e) (backward p e) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ha := (mem_forward p e i).mp hi
    have hb := (mem_backward p e i).mp hj
    omega
  have hsub : forward p e ∪ backward p e ⊆ p.support := by
    intro i hi
    apply Equiv.Perm.mem_support.mpr
    intro he
    rcases Finset.mem_union.mp hi with hi | hi
    · have hh := (mem_forward p e i).mp hi
      rw [he] at hh
      omega
    · have hh := (mem_backward p e i).mp hi
      rw [he] at hh
      omega
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,← cut_balance] at hh
  change halfLoad p e+halfLoad p e ≤ p.support.card at hh
  omega

theorem twice_left_peak_le_support (p : State n) (y : ℕ) : 2*leftPeak p y ≤ p.support.card := by
  have h : leftPeak p y ≤ p.support.card/2 := by
    apply Finset.sup_le
    intro e he
    have hh := twice_half_load_le_support p e
    omega
  omega

theorem twice_right_peak_le_support (p : State n) (x : ℕ) : 2*rightPeak p x ≤ p.support.card := by
  have h : rightPeak p x ≤ p.support.card/2 := by
    apply Finset.sup_le
    intro e he
    have hh := twice_half_load_le_support p e
    omega
  omega

theorem cycle_left_load_le_support (p : State n) (y : ℕ) : cycleLeftLoad p y ≤ (p.support.card : ℤ) := by
  unfold cycleLeftLoad
  calc
    _ ≤ ∑ q ∈ p.cycleFactorsFinset, (q.support.card : ℤ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast twice_left_peak_le_support q y
    _ = _ := by exact_mod_cast cycle_support_card_sum p

theorem cycle_right_load_le_support (p : State n) (x : ℕ) : cycleRightLoad p x ≤ (p.support.card : ℤ) := by
  unfold cycleRightLoad
  calc
    _ ≤ ∑ q ∈ p.cycleFactorsFinset, (q.support.card : ℤ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast twice_right_peak_le_support q x
    _ = _ := by exact_mod_cast cycle_support_card_sum p

theorem fixed_count_le_gapCost (p : State n) : n-p.support.card ≤ gapCost p := by
  have hl := cycle_left_load_le_support p n
  have hr := cycle_right_load_le_support p 0
  have hc : (n : ℤ)-(p.support.card : ℤ) ≤ cycleCharge p 0 n := by
    unfold cycleCharge
    simp only [Nat.cast_zero,zero_add,sub_zero]
    apply le_min <;> omega
  have hk := charge_le_gapCost p 0 n (Nat.zero_le _) le_rfl
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  omega

#print axioms twice_half_load_le_support
#print axioms fixed_count_le_gapCost
end LRX.FiniteCuts
