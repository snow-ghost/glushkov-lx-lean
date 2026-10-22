import LRX.ZeroGapInversionTerms

/-! Pair the two endpoint rows so all exterior inversion terms cancel. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem endpoint_row_terms (F : Fin n → ℤ) (v j : Fin n) (hv : 0 < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → F i=(i : ℤ)) :
    inversionTerm F 0 j+inversionTerm F v j=
      inversionTerm (swapEndpoints F v) 0 j+inversionTerm (swapEndpoints F v) v j+
      if 0 < j.val ∧ j.val ≤ v.val then 1 else 0 := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  by_cases hj0 : j=0
  · subst j
    have hvnot : ¬v < (0 : Fin n) := by change ¬v.val < 0; omega
    simp [inversionTerm,hvnot]
  · have hjpos : 0 < j.val := by have h : j.val ≠ 0 := fun h => hj0 (Fin.ext h); omega
    by_cases hjv : j=v
    · subst j
      obtain ⟨h1,h2⟩ := endpoint_terms F v hv hA hB hspan
      rw [h1,h2]
      simp [inversionTerm,hv]
    · by_cases hjlt : j.val < v.val
      · obtain ⟨h1,_,h2,_⟩ := interior_terms F v j hjpos hjlt hA hB hspan (hgap j hjpos hjlt)
        have hvj : ¬v < j := by change ¬v.val < j.val; omega
        rw [h1,h2]
        have hp : 0 < j.val ∧ j.val ≤ v.val := ⟨hjpos,Nat.le_of_lt hjlt⟩
        simp only [inversionTerm,ite_eq_right hvj,ite_eq_left hp]
      · have hvlt : v < j := by
          have hne : j.val ≠ v.val := fun h => hjv (Fin.ext h)
          change v.val < j.val
          omega
        have h0j : (0 : Fin n) < j := hjpos
        have hswap : Equiv.swap 0 v j=j := Equiv.swap_apply_of_ne_of_ne hj0 hjv
        simp only [inversionTerm,ite_eq_left h0j,ite_eq_left hvlt,swapEndpoints,hswap,
          Equiv.swap_apply_left,Equiv.swap_apply_right]
        have hnot : ¬(0 < j.val ∧ j.val ≤ v.val) := by omega
        simp only [ite_eq_right hnot,Nat.add_zero,Nat.zero_add,Nat.add_comm]

theorem other_row_terms (F : Fin n → ℤ) (v i j : Fin n)
    (hi0 : i ≠ 0) (hiv : i ≠ v)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ k : Fin n, 0 < k.val → k.val < v.val → F k=(k : ℤ)) :
    inversionTerm F i j=inversionTerm (swapEndpoints F v) i j+
      if 0 < i.val ∧ i.val < v.val then (if j=v then 1 else 0) else 0 := by
  have hipos : 0 < i.val := by have h : i.val ≠ 0 := fun h => hi0 (Fin.ext h); omega
  have hiswap : Equiv.swap 0 v i=i := Equiv.swap_apply_of_ne_of_ne hi0 hiv
  by_cases hj0 : j=0
  · subst j
    have hi : ¬i < (0 : Fin n) := by change ¬i.val < 0; omega
    by_cases hc : 0 < i.val ∧ i.val < v.val
    · have hv0 : (0 : Fin n) ≠ v := by intro he; have hz := congrArg Fin.val he; simp at hz; omega
      simp only [inversionTerm,ite_eq_right hi,ite_eq_left hc,ite_eq_right hv0,Nat.add_zero]
    · simp only [inversionTerm,ite_eq_right hi,ite_eq_right hc,Nat.add_zero]
  · by_cases hjv : j=v
    · subst j
      by_cases hlt : i.val < v.val
      · obtain ⟨_,h1,_,h2⟩ := interior_terms F v i hipos hlt hA hB hspan (hgap i hipos hlt)
        simp [h1,h2,hipos,hlt]
      · have hnot : ¬i < v := hlt
        simp [inversionTerm,hnot,hlt]
    · have hjswap : Equiv.swap 0 v j=j := Equiv.swap_apply_of_ne_of_ne hj0 hjv
      simp only [inversionTerm,swapEndpoints,hiswap,hjswap,ite_eq_right hjv]
      split_ifs <;> omega

#print axioms endpoint_row_terms
#print axioms other_row_terms
end LRX.ZeroGap
