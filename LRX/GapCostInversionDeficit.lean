import LRX.FiniteDepthSupport
import LRX.FiniteSupportPeakBounds
import Research.CayleyPy.GapInversionBudget

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem twice_choose_two_int (n : ℕ) : 2*(n.choose 2 : ℤ)=(n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    push_cast
    nlinarith

/-- Research lemma 11 for the actual permutation and the actual maximal
cursor charge, with all structural premises discharged. -/
theorem gapCost_triangular_inversion_deficit (p : State n) :
    (gapCost p : ℤ)*((gapCost p : ℤ)-1) ≤ 2*((n.choose 2 : ℤ)-(inversionNumber p : ℤ)) := by
  have hquad := gapCost_quadratic p
  have hd := finite_depth_support p
  have hf := fixed_count_le_gapCost p
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hdepth : 2*(inversionNumber p : ℤ) ≤
      2*(∑ i : Fin n, |displacement p i|)-(n : ℤ)+(gapCost p : ℤ) := by omega
  exact CayleyPy.GapInversionBudget.triangular_inversion_deficit (n : ℤ)
    (∑ i : Fin n, |displacement p i|) (inversionNumber p : ℤ) (gapCost p : ℤ)
    (n.choose 2 : ℤ) hquad hdepth (twice_choose_two_int n)

theorem inversion_deficit_nonneg (p : State n) : 0 ≤ (n.choose 2 : ℤ)-(inversionNumber p : ℤ) := by
  have ht := gapCost_triangular_inversion_deficit p
  by_cases hz : gapCost p=0
  · rw [hz] at ht
    norm_num at ht ⊢
    omega
  · have hp : 0 ≤ (gapCost p : ℤ)*((gapCost p : ℤ)-1) :=
      mul_nonneg (by positivity) (by omega)
    omega

theorem gapCost_le_inversion_deficit (p : State n) :
    (gapCost p : ℤ) ≤ (n.choose 2 : ℤ)-(inversionNumber p : ℤ)+1 :=
  CayleyPy.GapInversionBudget.integer_linear_deficit _ _ (inversion_deficit_nonneg p)
    (gapCost_triangular_inversion_deficit p)

theorem inversion_number_le_choose_two (p : State n) : inversionNumber p ≤ n.choose 2 := by
  have hh := inversion_deficit_nonneg p
  exact_mod_cast (show (inversionNumber p : ℤ) ≤ (n.choose 2 : ℤ) by omega)

#print axioms gapCost_triangular_inversion_deficit
#print axioms gapCost_le_inversion_deficit
end LRX.FiniteCuts
