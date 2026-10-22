import LRX.ComponentInversionBudget
import LRX.FiniteReversalBounds

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- All cross-cut ordered pairs are absent from the inversion set. -/
theorem inversion_budget_of_invariant_cut (p : State n) (a : ℕ) (ha : a ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    (inversionNumber p : ℤ) ≤ (a.choose 2 : ℤ) + ((n-a).choose 2 : ℤ) := by
  have hleft : (∑ i : Fin n, if i.val < a then (1 : ℤ) else 0) = (a : ℤ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_filter_val_lt,
      Nat.min_eq_right ha]
  have hright : (∑ j : Fin n, if a ≤ j.val then (1 : ℤ) else 0) = ((n-a : ℕ) : ℤ) := by
    have hpoint (j : Fin n) : (if a ≤ j.val then (1 : ℤ) else 0) =
        1 - (if j.val < a then 1 else 0) := by split_ifs <;> omega
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, hleft]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    omega
  have hcross : (∑ i : Fin n, ∑ j : Fin n,
      (if i.val < a then (1 : ℤ) else 0) * (if a ≤ j.val then (1 : ℤ) else 0)) =
      (a : ℤ) * ((n-a : ℕ) : ℤ) := by
    simp_rw [← Finset.mul_sum, hright]
    rw [← Finset.sum_mul, hleft]
  have hpoint (i j : Fin n) : inversionIndicator p i j +
      (if i.val < a then (1 : ℤ) else 0) * (if a ≤ j.val then (1 : ℤ) else 0) ≤
      if i.val < j.val then (1 : ℤ) else 0 := by
    have hno : i.val < a → a ≤ j.val → ¬((p j).val < (p i).val) := by
      intro hi hj
      have hpi := (hcut i).mpr hi
      have hpj := (hcut j).not.mpr (by omega)
      omega
    unfold inversionIndicator
    split_ifs <;> norm_num <;> omega
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
  simp only [Finset.sum_add_distrib] at h
  rw [sum_inversion_indicator, hcross] at h
  have hordered : (∑ i : Fin n, ∑ j : Fin n,
      if i.val < j.val then (1 : ℤ) else 0) = (n.choose 2 : ℤ) := by
    exact_mod_cast ordered_pair_sum n
  rw [hordered] at h
  have hid := two_block_choose_identity (n := n) a ha
  omega

/-- At odd size the two nearly equal blocks have exactly enough inversion reserve. -/
theorem two_block_sharp_word_odd (m : ℕ) (hm : 2 ≤ m) (hn : n = 2*m+1)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < m+1 ↔ i.val < m+1)
    (start finish : Fin n) :
    ∃ w : List Letter, eval w = (RotationWords.rotation start)⁻¹ * p * RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 := by
  apply two_block_sharp_word_of_inversion_bound (m+1) (by omega) (by omega) p hcut ?_ start finish
  have hI := inversion_budget_of_invariant_cut p (m+1) (by omega) hcut
  have hA := twice_choose_two_int (m+1)
  have hB := twice_choose_two_int (n-(m+1))
  have hb : n-(m+1) = m := by omega
  have hh : n/2 = m := by omega
  rw [hb, hh]
  rw [hb] at hB hI
  push_cast at hA ⊢
  nlinarith

#print axioms inversion_budget_of_invariant_cut
#print axioms two_block_sharp_word_odd
end LRX.FiniteCuts
