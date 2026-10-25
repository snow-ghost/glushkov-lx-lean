import LRX.FiniteDescentRank
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Integer indicator of an ordinary inversion. -/
def inversionIndicator (p : State n) (i j : Fin n) : ℤ :=
  if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0

@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]

theorem sum_inversion_indicator (p : State n) :
    (∑ i, ∑ j, inversionIndicator p i j)=(inversionNumber p : ℤ) := by
  simp only [inversionNumber, inversionIndicator, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Incoming minus outgoing inversions equals the leftward displacement. -/
theorem inversion_row_balance (p : State n) (i : Fin n) :
    (∑ j, inversionIndicator p j i)-(∑ j, inversionIndicator p i j) =
      (i : ℤ)-(p i : ℤ) := by
  have hpoint (j : Fin n) : inversionIndicator p j i-inversionIndicator p i j =
      (if j.val < i.val then (1 : ℤ) else 0)-
      (if (p j).val < (p i).val then (1 : ℤ) else 0) := by
    by_cases h : i=j
    · subst j; simp [inversionIndicator]
    have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
    have hp : (p i).val ≠ (p j).val := fun he => h (p.injective (Fin.ext he))
    unfold inversionIndicator
    split_ifs <;> omega
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  have hcount (a : Fin n) : (∑ j : Fin n, if j.val < a.val then (1 : ℤ) else 0)=(a : ℤ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (Fin.card_filter_val_lt (n := n) (m := a.val)).trans (Nat.min_eq_right (Nat.le_of_lt a.isLt))
  rw [hcount]
  have hp := Equiv.sum_comp p (fun j : Fin n => if j.val < (p i).val then (1 : ℤ) else 0)
  rw [hp, hcount]

/-- Indicator of a position whose image lies to its left. -/
def descendingIndicator (p : State n) (i : Fin n) : ℤ :=
  if (p i).val < i.val then 1 else 0

theorem sum_descending_indicator (p : State n) :
    (∑ i, descendingIndicator p i)=((descendingPositions p).card : ℤ) := by
  unfold descendingIndicator
  rw [← Finset.sum_filter]
  simp [descendingPositions]

theorem weighted_displacement_eq_leftDepth (p : State n) :
    (∑ i, descendingIndicator p i*((i : ℤ)-(p i : ℤ)))=leftDepth p := by
  simp only [leftDepth, descendingPositions, Finset.sum_filter, descendingIndicator,
    ite_mul, one_mul, zero_mul]

/-- Internal inversions cancel when row balances are summed over left-moving positions. -/
theorem weighted_inversion_balance (p : State n) :
    (∑ i, ∑ j, inversionIndicator p i j*(descendingIndicator p j-descendingIndicator p i))=
      leftDepth p := by
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => inversionIndicator p i j*descendingIndicator p j)]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, inversion_row_balance, mul_comm]
  exact weighted_displacement_eq_leftDepth p

#print axioms inversion_row_balance
#print axioms weighted_inversion_balance
end LRX.FiniteCuts
