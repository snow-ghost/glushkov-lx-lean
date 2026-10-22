import LRX.FiniteRankSorting

namespace LRX.FiniteRankOrder
open scoped BigOperators
variable {n : ℕ}

/-- Count points of the permutation matrix in a prefix rectangle. -/
noncomputable def rectangle (p : State n) (k l : ℕ) : ℕ :=
  ∑ i : Fin n, if i.val < k ∧ (p i).val < l then 1 else 0

theorem rectangle_inverse (p : State n) (k l : ℕ) :
    rectangle p⁻¹ l k=rectangle p k l := by
  classical
  unfold rectangle
  have h := Equiv.sum_comp p (fun j : Fin n =>
    if j.val < l ∧ (p⁻¹ j).val < k then (1 : ℕ) else 0)
  simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply,and_comm] using h.symm

theorem rank_add_rectangle (p : State n) (k t : ℕ) :
    rank p k t+rectangle p k (t+1)=min n k := by
  classical
  unfold rank rectangle
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin n, if i.val < k then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k <;> by_cases ht : t < (p i).val <;>
        simp [hi,ht,show (p i).val < t+1 ↔ ¬t < (p i).val by omega]
    _ = min n k := by simp [Fin.card_filter_val_lt]

theorem rectangle_antitone {p q : State n} (hpq : Below p q) (k l : ℕ) :
    rectangle q k l ≤ rectangle p k l := by
  by_cases hl : l=0
  · subst l; simp [rectangle]
  · have hp := rank_add_rectangle p k (l-1)
    have hq := rank_add_rectangle q k (l-1)
    have h := hpq k (l-1)
    have he : l-1+1=l := by omega
    rw [he] at hp hq
    omega

theorem below_inverse {p q : State n} (hpq : Below p q) : Below p⁻¹ q⁻¹ := by
  intro k t
  have hr := rectangle_antitone hpq (t+1) k
  have hp := rank_add_rectangle p⁻¹ k t
  have hq := rank_add_rectangle q⁻¹ k t
  rw [rectangle_inverse] at hp hq
  omega

theorem below_inverse_iff (p q : State n) : Below p⁻¹ q⁻¹ ↔ Below p q := by
  constructor
  · intro h
    simpa only [inv_inv] using below_inverse h
  · exact below_inverse

#print axioms rectangle_inverse
#print axioms below_inverse_iff
end LRX.FiniteRankOrder
