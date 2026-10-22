import Mathlib

/-!
Phase51: arithmetic for paying every invariant finite packet gap.
The quadratic load lemma, finite depth inequality and strict-band
inversion capacity are mathematical premises, not formalized here.
The completion is used only to certify an inversion budget; the route
still serves the original fillers in the original integer lift.
-/
namespace CayleyPy.GapInversionBudget

theorem depth_with_cursor (b fixed rank Delta I K : ℤ)
    (hrank : b-fixed ≤ 2*rank) (hdepth : I+rank ≤ Delta)
    (hfixed : fixed ≤ K) :
    2*I ≤ 2*Delta-b+K := by omega

theorem triangular_inversion_deficit (b Delta I K B : ℤ)
    (hquad : 2*Delta+K^2 ≤ b^2)
    (hdepth : 2*I ≤ 2*Delta-b+K)
    (hB : 2*B=b*(b-1)) :
    K*(K-1) ≤ 2*(B-I) := by nlinarith

theorem integer_linear_deficit (K d : ℤ) (hd : 0 ≤ d)
    (htri : K*(K-1) ≤ 2*d) : K ≤ d+1 := by
  by_cases hK : K ≤ 1
  · omega
  · have hp := mul_nonneg (show 0 ≤ K-1 by omega)
      (show 0 ≤ K-2 by omega)
    nlinarith

theorem completion_budget (Q m original root fillers reversed total : ℤ)
    (horiginal : original=root+fillers)
    (hcompleted : total=root+reversed)
    (hcap : total ≤ Q-m) :
    reversed-fillers ≤ Q-m-original := by omega

theorem internal_gap_paid (K deficit totalDeficit delta epsilon w : ℤ)
    (hK : K ≤ deficit+1) (hlocal : deficit ≤ totalDeficit)
    (hcompletion : totalDeficit ≤ delta)
    (hepsilon : 0 ≤ epsilon) (hw : 2 ≤ w) :
    K-w ≤ delta+epsilon-1 := by omega

theorem source_word_bound (N I Delta K w length delta epsilon : ℤ)
    (hbudget : N-I-Delta=delta+epsilon)
    (hcharge : K-w ≤ delta+epsilon-1)
    (hword : length ≤ I+Delta+K-w) : length ≤ N-1 := by omega

theorem same_budget_identity (Q m I Delta : ℤ) :
    (2*Q-m)-I-Delta=(Q-m-I)+(Q-Delta) := by ring

#print axioms depth_with_cursor
#print axioms triangular_inversion_deficit
#print axioms integer_linear_deficit
#print axioms completion_budget
#print axioms internal_gap_paid
#print axioms source_word_bound
#print axioms same_budget_identity

end CayleyPy.GapInversionBudget
