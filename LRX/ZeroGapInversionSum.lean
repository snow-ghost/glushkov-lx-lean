import LRX.ZeroGapInversionRows

/-! Summing the zero-gap row identities gives the exact inversion decrease. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def otherIndices (v : Fin n) : Finset (Fin n) := (Finset.univ.erase 0).erase v

theorem sum_two_and_others (f : Fin n → ℕ) (v : Fin n) (hv : v ≠ 0) :
    (∑ i, f i)=f 0+f v+∑ i ∈ otherIndices v, f i := by
  have h0 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : Fin n))
  have hv' := Finset.sum_erase_add (Finset.univ.erase 0) f (by simp [hv] : v ∈ Finset.univ.erase 0)
  unfold otherIndices
  omega

theorem count_positive_below (t : ℕ) (ht0 : 0 < t) (htn : t ≤ n) :
    (∑ i : Fin n, if 0 < i.val ∧ i.val < t then (1 : ℕ) else 0)= (t-1 : ℕ) := by
  rw [Finset.sum_boole]
  have he : (Finset.univ.filter (fun i : Fin n => 0 < i.val ∧ i.val < t))=
      (Finset.univ.filter (fun i : Fin n => i.val < t)).erase 0 := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,ne_eq,Fin.ext_iff,Fin.val_zero]
    omega
  rw [he,Finset.card_erase_of_mem (by simp [ht0]),Fin.card_filter_val_lt,min_eq_right htn]
  simp

theorem count_others_below (v : Fin n) (hv : 0 < v.val) :
    (∑ i ∈ otherIndices v, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0)= (v.val-1 : ℕ) := by
  have he : (∑ i ∈ otherIndices v, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0)=
      ∑ i : Fin n, if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hnot
    by_cases hp : 0 < i.val ∧ i.val < v.val
    · have hi0 : i ≠ 0 := by intro h; subst i; simp at hp
      have hiv : i ≠ v := by intro h; subst i; omega
      exact False.elim (hnot (by simp [otherIndices,hi0,hiv]))
    · simp only [ite_eq_right hp]
  rw [he]
  exact count_positive_below v.val hv (Nat.le_of_lt v.isLt)

theorem endpoint_swap_inversions (F : Fin n → ℤ) (v : Fin n) (hv : 0 < v.val)
    (hA : (v : ℤ) ≤ F 0) (hB : F v ≤ 0) (hspan : F 0-F v < (n : ℤ))
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → F i=(i : ℤ)) :
    LiftedModel.inversionCount F=LiftedModel.inversionCount (swapEndpoints F v)+(2*v.val-1) := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  let row := fun i => ∑ j : Fin n, inversionTerm F i j
  let row' := fun i => ∑ j : Fin n, inversionTerm (swapEndpoints F v) i j
  have hend : row 0+row v=row' 0+row' v+v.val := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun j _ => endpoint_row_terms F v j hv hA hB hspan hgap)
    simp only [Finset.sum_add_distrib] at h
    have hc : (∑ j : Fin n, if 0 < j.val ∧ j.val ≤ v.val then (1 : ℕ) else 0)=v.val := by
      have hh := count_positive_below (n := n) (v.val+1) (by omega) v.isLt
      simpa only [Nat.lt_add_one_iff,Nat.add_sub_cancel] using hh
    rw [hc] at h
    exact h
  have hother : ∀ i ∈ otherIndices v, row i=row' i+(if 0 < i.val ∧ i.val < v.val then (1 : ℕ) else 0) := by
    intro i hi
    have hiv : i ≠ v := (Finset.mem_erase.mp hi).1
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun j _ => other_row_terms F v i j hi0 hiv hA hB hspan hgap)
    rw [Finset.sum_add_distrib] at h
    by_cases hp : 0 < i.val ∧ i.val < v.val
    · simpa only [ite_eq_left hp,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h
    · simpa only [ite_eq_right hp,Finset.sum_const_zero] using h
  have hs := Finset.sum_congr rfl hother
  rw [Finset.sum_add_distrib,count_others_below v hv] at hs
  have ho := sum_two_and_others row v hv0
  have hn := sum_two_and_others row' v hv0
  change (∑ i, row i)=(∑ i, row' i)+(2*v.val-1)
  calc
    (∑ i, row i) = row 0+row v+∑ i ∈ otherIndices v, row i := ho
    _ = (row 0+row v)+((∑ i ∈ otherIndices v, row' i)+(v.val-1)) := by rw [hs]
    _ = (row' 0+row' v+v.val)+((∑ i ∈ otherIndices v, row' i)+(v.val-1)) := by rw [hend]
    _ = (row' 0+row' v+∑ i ∈ otherIndices v, row' i)+(2*v.val-1) := by omega
    _ = (∑ i, row' i)+(2*v.val-1) := by rw [← hn]

#print axioms endpoint_swap_inversions
end LRX.ZeroGap
