import LX.DepthBound
import LX.SweepCarrier
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem ascending_depth_le (hn : 2 ≤ n) (d : Fin n → ℤ)
    (horder : targets d 0 < targets d 1) : backwardDepth d 1 ≤ backwardDepth d 0 := by
  rw [backward_depth_formula, backward_depth_head]
  have hnz : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j=0
  · subst j
    have hjlt : (0 : Fin n)<1 := by change 0 < (1 : Fin n).val; omega
    have hq : (targets d 0-targets d 1)/(n : ℤ) < 0 :=
      (Int.ediv_lt_iff_lt_mul hnz).mpr (by omega)
    simp only [hjlt, ite_true, sub_self, Int.zero_ediv, Int.toNat_zero]
    omega
  · have hjn : ¬ j<1 := by
      have h0 : j.val≠0 := fun he => hj (Fin.ext he)
      change ¬ j.val < (1 : Fin n).val
      omega
    simp only [hjn, ite_false, add_zero]
    apply Int.toNat_le_toNat
    exact Int.ediv_le_ediv hnz (by omega)

/-- A forward exchange preserves the carried token's backward depth. -/
theorem exchange_forward_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1+1 < d 0) : backwardDepth (exchange d) 1 = backwardDepth d 0 := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap 0 1
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hnz : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq : (targets d 1-targets d 0)/(n : ℤ) < 0 := by
    apply (Int.ediv_lt_iff_lt_mul hnz).mpr
    simp only [targets, Fin.val_zero, Nat.cast_zero, zero_add, hv1, Nat.cast_one]
    omega
  have horder (j : Fin n) : τ j < 1 ↔ j=1 := by
    by_cases hj1 : j=1
    · subst j
      simp only [τ, Equiv.swap_apply_right, Fin.lt_def, Fin.val_zero, hv1]
      simp
    · by_cases hj0 : j=0
      · subst j
        simp [τ, hj1]
      · simp only [τ, Equiv.swap_apply_of_ne_of_ne hj0 hj1, hj1, iff_false, Fin.lt_def]
        have h0 : j.val≠0 := fun he => hj0 (Fin.ext he)
        omega
  rw [backward_depth_formula, backward_depth_head]
  simp only [exchange_targets hn, Equiv.swap_apply_right]
  rw [← Equiv.sum_comp τ (fun j =>
    ((targets d (τ j)-targets d 0)/(n : ℤ) + if j<1 then 1 else 0).toNat)]
  simp only [τ, Equiv.swap_apply_self] at horder ⊢
  apply Finset.sum_congr rfl
  intro j _
  simp only [horder]
  by_cases hj : j=1
  · subst j
    simp only [ite_true]
    omega
  · simp only [hj, ite_false, add_zero]

/-- The carrier's backward depth is the minimum of the two compared depths. -/
theorem sweep_step_head_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) :
    backwardDepth (sweepStep d) 0 = min (backwardDepth d 0) (backwardDepth d 1) := by
  have hv1 : ((1 : Fin n) : ℤ)=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h01 : (0 : Fin n)≠1 := by intro he; have := Fin.one_eq_zero_iff.mp he.symm; omega
  have hne : targets d 0 ≠ targets d 1 := by
    intro he
    have hh := congrArg (fun z : ℤ => (z : Fin n)) he
    have hcast (i : Fin n) : ((targets d i : ℤ) : Fin n)=labels d i := by simp [targets,labels]
    rw [hcast,hcast] at hh
    exact h01 (hi hh)
  have ht : targets d 0=d 0 ∧ targets d 1=1+d 1 := by simp [targets, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hr : backwardDepth (sweepStep d) 0 = backwardDepth (compareHead d) 1 := by
    rw [sweepStep,rotate_backward_depth hn]
    simp [finRotate_apply]
  rw [hr]
  unfold compareHead
  split_ifs with hdesc
  · rw [exchange_forward_depth hn d hdesc]
    have hh := backward_depth_gt_head d 1 (by omega)
    exact (min_eq_left (le_of_lt hh)).symm
  · have hh := ascending_depth_le hn d (by omega)
    exact (min_eq_right hh).symm

#print axioms ascending_depth_le
#print axioms exchange_forward_depth
#print axioms sweep_step_head_depth
end LX.AffineScan
