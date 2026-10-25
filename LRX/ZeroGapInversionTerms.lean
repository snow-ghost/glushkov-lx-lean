import Mathlib

/-! The inversion terms reversed by a zero-gap endpoint swap each drop from
one to zero. Other endpoint terms are exchanged in pairs. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def inversionTerm (F : Fin n → ℤ) (i j : Fin n) : ℕ :=
  if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0

def swapEndpoints (F : Fin n → ℤ) (v i : Fin n) : ℤ := F (Equiv.swap 0 v i)

theorem negative_quotient_term {z : ℤ} (hz : z < 0) (hn : -z ≤ (n : ℤ)) : (z/(n : ℤ)).natAbs=1 := by
  rw [Int.ediv_eq_neg_one_of_neg_of_le hz hn]
  decide

theorem nonnegative_quotient_term {z : ℤ} (hz : 0 ≤ z) (hn : z < (n : ℤ)) : (z/(n : ℤ)).natAbs=0 := by
  rw [Int.ediv_eq_zero_of_lt hz hn]
  decide

theorem endpoint_terms (F : Fin n → ℤ) (v : Fin n) (hv : 0 < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ)) :
    inversionTerm F 0 v=1 ∧ inversionTerm (swapEndpoints F v) 0 v=0 := by
  have hv0 : (0 : Fin n) < v := hv
  constructor
  · rw [inversionTerm,ite_eq_left hv0]
    exact negative_quotient_term (by omega) (by omega)
  · simp only [inversionTerm,ite_eq_left hv0,swapEndpoints,Equiv.swap_apply_left,Equiv.swap_apply_right]
    exact nonnegative_quotient_term (by omega) hspan

theorem interior_terms (F : Fin n → ℤ) (v j : Fin n)
    (hj0 : 0 < j.val) (hjv : j.val < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ)) (hF : F j=(j : ℤ)) :
    inversionTerm F 0 j=1 ∧ inversionTerm F j v=1 ∧
      inversionTerm (swapEndpoints F v) 0 j=0 ∧ inversionTerm (swapEndpoints F v) j v=0 := by
  have h0j : (0 : Fin n) < j := hj0
  have hjv' : j < v := hjv
  have hjne0 : j ≠ 0 := ne_of_gt h0j
  have hjnev : j ≠ v := ne_of_lt hjv'
  have hswap : Equiv.swap 0 v j=j := Equiv.swap_apply_of_ne_of_ne hjne0 hjnev
  refine ⟨?_,?_,?_,?_⟩
  · rw [inversionTerm,ite_eq_left h0j,hF]
    exact negative_quotient_term (by omega) (by omega)
  · rw [inversionTerm,ite_eq_left hjv',hF]
    exact negative_quotient_term (by omega) (by omega)
  · simp only [inversionTerm,ite_eq_left h0j,swapEndpoints,hswap,Equiv.swap_apply_left,hF]
    exact nonnegative_quotient_term (by omega) (by omega)
  · simp only [inversionTerm,ite_eq_left hjv',swapEndpoints,hswap,Equiv.swap_apply_right,hF]
    exact nonnegative_quotient_term (by omega) (by omega)

#print axioms endpoint_terms
#print axioms interior_terms
end LRX.ZeroGap
