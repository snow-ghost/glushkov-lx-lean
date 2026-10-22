import Research.CayleyPy.BalancedTwoBlockPorts

namespace LRX.TwoBlockPorts
open BalancedTwoBlockPorts

/-- The four center pairs cover arbitrary cursor approaches for all two-block sizes. -/
theorem four_center_cover (a b s t : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hs : 0 ≤ s) (hsn : s < a+b) (ht : 0 ≤ t) (htn : t < a+b) :
    lee (a+b) s ((a-1)/2)+lee (a+b) t (a+(b-2)/2) ≤ (a+b)/2 ∨
    lee (a+b) s (a+(b-2)/2)+lee (a+b) t ((a-1)/2) ≤ (a+b)/2 ∨
    lee (a+b) s (a+(b-1)/2)+lee (a+b) t ((a-2)/2) ≤ (a+b)/2 ∨
    lee (a+b) s ((a-2)/2)+lee (a+b) t (a+(b-1)/2) ≤ (a+b)/2 := by
  have hm : 1 ≤ (a+b)/2 := by omega
  have hpar : a+b=2*((a+b)/2) ∨ a+b=2*((a+b)/2)+1 := by omega
  rcases hpar with he | ho
  · have h1 := even_antipodes ((a+b)/2) s ((a-1)/2) hm hs (by omega) (by omega) (by omega)
    have h2 := even_antipodes ((a+b)/2) t ((a-2)/2) hm ht (by omega) (by omega) (by omega)
    have hB1 : a+(b-1)/2=(a-1)/2+(a+b)/2 := by omega
    have hB0 : a+(b-2)/2=(a-2)/2+(a+b)/2 := by omega
    rw [← he,← hB1] at h1
    rw [← he,← hB0] at h2
    omega
  · have hapar : a=2*(a/2) ∨ a=2*(a/2)+1 := by omega
    rcases hapar with hae | hao
    · have hA : (a-1)/2=(a-2)/2 := by omega
      have hB0 : a+(b-2)/2=(a-2)/2+(a+b)/2 := by omega
      have hB1 : a+(b-1)/2=(a-2)/2+(a+b)/2+1 := by omega
      have h1 := odd_one_two ((a+b)/2) s ((a-2)/2) hm hs (by omega) (by omega) (by omega)
      have h2 := odd_one_two ((a+b)/2) t ((a-2)/2) hm ht (by omega) (by omega) (by omega)
      have hBstep : a+(b-1)/2=a+(b-2)/2+1 := by omega
      rw [← ho,← hB0,← hBstep] at h1 h2
      rw [hA]
      omega
    · have hA : (a-1)/2=(a-2)/2+1 := by omega
      have hB : a+(b-1)/2=a+(b-2)/2 := by omega
      have hB0 : a+(b-2)/2=(a-2)/2+(a+b)/2+1 := by omega
      have h1 := odd_two_one ((a+b)/2) s ((a-2)/2) hm hs (by omega) (by omega) (by omega)
      have h2 := odd_two_one ((a+b)/2) t ((a-2)/2) hm ht (by omega) (by omega) (by omega)
      rw [← ho,← hA,← hB0] at h1 h2
      rw [hB]
      omega

#print axioms four_center_cover
end LRX.TwoBlockPorts
