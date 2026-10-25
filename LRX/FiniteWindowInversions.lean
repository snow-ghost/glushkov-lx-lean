import LRX.FiniteWindow
import LRX.InversionSet
import LRX.ZeroGapInversionTerms
import Mathlib

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

def inversionNumber (p : State n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0

theorem canonical_inversion_term [NeZero n] (p : State n) (i j : Fin n) :
    (if i < j then (((p j : ℤ)-(p i : ℤ))/(n : ℤ)).natAbs else 0)=
      if i.val < j.val ∧ (p j).val < (p i).val then 1 else 0 := by
  have hi0 : (0 : ℤ) ≤ p i := by positivity
  have hj0 : (0 : ℤ) ≤ p j := by positivity
  have hin : (p i : ℤ) < n := by exact_mod_cast (p i).isLt
  have hjn : (p j : ℤ) < n := by exact_mod_cast (p j).isLt
  by_cases hij : i.val < j.val
  · have hij' : i < j := hij
    rw [if_pos hij']
    by_cases hp : (p j).val < (p i).val
    · have hp' : (p j : ℤ) < p i := by exact_mod_cast hp
      rw [ZeroGap.negative_quotient_term (by omega) (by omega)]
      simp [hij,hp]
    · have hp' : (p i : ℤ) ≤ p j := by exact_mod_cast (show (p i).val ≤ (p j).val by omega)
      rw [ZeroGap.nonnegative_quotient_term (by omega) (by omega)]
      simp [hij,hp]
  · have hij' : ¬i < j := hij
    simp [hij',hij]

theorem canonical_inversion_count [NeZero n] (p : State n) :
    LiftedModel.inversionCount (fun i : Fin n => (p i : ℤ))=inversionNumber p := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact canonical_inversion_term p i j
end LRX.FiniteCuts

namespace LRX.FiniteWindow
open scoped BigOperators
variable {n b : ℕ}

theorem sum_window_nat (W : Window n b) (f : Fin n → ℕ)
    (hzero : ∀ j, ¬Contains W j → f j=0) :
    (∑ j : Fin n, f j)=∑ i : Fin b, f (embed W i) := by
  classical
  let S := Finset.univ.image (embed W)
  have hsub : (∑ j ∈ S, f j)=∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    apply hzero j
    intro h
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp h
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [← hsub]
  exact Finset.sum_image (fun i _ j _ h => embed_injective W h)

theorem contains_permutation (W : Window n b) (p : State b) (i : Fin n)
    (hi : Contains W i) : Contains W (permutation W p i) := by
  obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
  rw [permutation_embed]
  exact contains_embed W (p j)

theorem no_outside_inversion (W : Window n b) (p : State b) (i j : Fin n)
    (hout : ¬Contains W i ∨ ¬Contains W j) :
    ¬(i.val < j.val ∧ (permutation W p j).val < (permutation W p i).val) := by
  intro h
  rcases hout with hi | hj
  · rw [permutation_outside W p i hi] at h
    by_cases hj : Contains W j
    · have hpj := contains_permutation W p j hj
      unfold Contains at hi hj hpj
      omega
    · rw [permutation_outside W p j hj] at h
      omega
  · rw [permutation_outside W p j hj] at h
    by_cases hi : Contains W i
    · have hpi := contains_permutation W p i hi
      unfold Contains at hi hj hpi
      omega
    · rw [permutation_outside W p i hi] at h
      omega

theorem inversion_number_window (W : Window n b) (p : State b) :
    FiniteCuts.inversionNumber (permutation W p)=FiniteCuts.inversionNumber p := by
  unfold FiniteCuts.inversionNumber
  rw [sum_window_nat W _ (by
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (no_outside_inversion W p i j (Or.inl hi)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_window_nat W _ (by
    intro j hj
    exact if_neg (no_outside_inversion W p (embed W i) j (Or.inr hj)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [permutation_embed]
  simp [embed]

#print axioms inversion_number_window
end LRX.FiniteWindow
