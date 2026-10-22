import LRX.FiniteRankOrder
import LRX.FiniteReversalBounds

namespace LRX.FiniteRankOrder
open scoped BigOperators
variable {n : ℕ}

theorem rank_eq_card (p : State n) (k t : ℕ) :
    rank p k t=(Finset.univ.filter (fun i : Fin n => i.val < k ∧ t < (p i).val)).card := by
  unfold rank
  rw [← Finset.sum_filter]
  simp

theorem upper_value_count (n t : ℕ) :
    (Finset.univ.filter (fun i : Fin n => t < i.val)).card=n-(t+1) := by
  have heq : Finset.univ.filter (fun i : Fin n => t < i.val)=
      Finset.univ \ Finset.univ.filter (fun i : Fin n => i.val < t+1) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [heq,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),Finset.card_univ,
    Fintype.card_fin,Fin.card_filter_val_lt]
  omega

theorem rank_capacity (p : State n) (k t : ℕ) : rank p k t ≤ min k (n-(t+1)) := by
  classical
  have hprefix : rank p k t ≤ k := by
    have hs : Finset.univ.filter (fun i : Fin n => i.val < k ∧ t < (p i).val) ⊆
        Finset.univ.filter (fun i : Fin n => i.val < k) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1⟩
    have hc := Finset.card_le_card hs
    rw [← rank_eq_card,Fin.card_filter_val_lt] at hc
    omega
  have htarget : rank p k t ≤ n-(t+1) := by
    have hs : rank p k t ≤ ∑ i : Fin n, if t < (p i).val then (1 : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs  <;> omega
    rw [Equiv.sum_comp p (fun i : Fin n => if t < i.val then (1 : ℕ) else 0),
      ← Finset.sum_filter] at hs
    simp only [Finset.sum_const,smul_eq_mul,mul_one,upper_value_count] at hs
    exact hs
  exact le_min hprefix htarget

/-- Reversal attains every prefix rank bound at once. -/
theorem rank_reversal (n k t : ℕ) : rank (Fin.revPerm : State n) k t=min k (n-(t+1)) := by
  have hpoint (i : Fin n) :
      (i.val < k ∧ t < ((Fin.revPerm : State n) i).val) ↔ i.val < min k (n-(t+1)) := by
    change (i.val < k ∧ t < i.rev.val) ↔ _
    simp only [Fin.val_rev]
    have hi := i.isLt
    omega
  rw [rank_eq_card]
  simp only [hpoint,Fin.card_filter_val_lt]
  omega

/-- Every finite target is below reversal in the rank order used by M1. -/
theorem below_reversal (p : State n) : Below p Fin.revPerm := by
  intro k t
  rw [rank_reversal]
  exact rank_capacity p k t

#print axioms below_reversal
end LRX.FiniteRankOrder
