import LRX.FiniteInversionBalance
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Summing a symmetric pair contribution over i < j counts each directed pair once. -/
theorem sum_upper_sym (f : Fin n → Fin n → ℤ) (hd : ∀ i, f i i=0) :
    (∑ i, ∑ j, if i < j then f i j+f j i else 0) = ∑ i, ∑ j, f i j := by
  have hsplit (i j : Fin n) : (if i < j then f i j+f j i else 0)=
      (if i < j then f i j else 0)+(if i < j then f j i else 0) := by
    split_ifs <;> simp
  have hpoint (i j : Fin n) :
      (if i < j then f i j else 0)+(if j < i then f i j else 0)=f i j := by
    by_cases heq : i=j
    · subst j; simp [hd]
    have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
    by_cases hlt : i < j
    · have hnot : ¬j < i := not_lt.mpr (le_of_lt hlt)
      simp [hlt,hnot]
    · have hrev : j < i := by change j.val < i.val; change ¬i.val < j.val at hlt; omega
      simp [hlt,hrev]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j i else 0)]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, hpoint]

def crossPairIndicator (p : State n) (i j : Fin n) : ℤ :=
  if i < j then descendingIndicator p i*(1-descendingIndicator p j)+
    descendingIndicator p j*(1-descendingIndicator p i) else 0

/-- There are |D|(n-|D|) unordered pairs with exactly one endpoint in D. -/
theorem sum_cross_pair_indicator (p : State n) :
    (∑ i, ∑ j, crossPairIndicator p i j)=
      ((descendingPositions p).card : ℤ)*((n : ℤ)-(descendingPositions p).card) := by
  unfold crossPairIndicator
  rw [sum_upper_sym (fun i j => descendingIndicator p i*(1-descendingIndicator p j))
    (fun i => by unfold descendingIndicator; split_ifs <;> norm_num)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_descending_indicator, Finset.sum_sub_distrib,
    sum_descending_indicator]
  simp

#print axioms sum_cross_pair_indicator
end LRX.FiniteCuts
