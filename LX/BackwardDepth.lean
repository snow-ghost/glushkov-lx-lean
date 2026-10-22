import LX.SweepCarrier

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Number of inverted predecessors of a lifted token, counted over the preceding periods. -/
def backwardDepth (d : Fin n → ℤ) (i : Fin n) : ℕ :=
  ∑ j : Fin n, (-LRX.AffineLift.crossing d i j).toNat

theorem crossing_quotient (d : Fin n → ℤ) (i j : Fin n) :
    -LRX.AffineLift.crossing d i j =
      (targets d j-targets d i)/(n : ℤ) + if j < i then 1 else 0 := by
  simp only [LRX.AffineLift.crossing, neg_neg, LRX.AffineLift.crossingNumerator,
    Fin.intCast_val_sub_eq_sub_add_ite]
  by_cases hji : j < i
  · have hh : ¬ i ≤ j := not_le.mpr hji
    simp only [hh, ite_false, hji, ite_true]
    have he : (j : ℤ)-(i : ℤ)+(n : ℤ)+d j-d i = targets d j-targets d i+n := by
      unfold targets
      ring
    rw [he]
    simpa only [one_mul] using Int.add_mul_ediv_right
      (targets d j-targets d i) 1 (by exact_mod_cast NeZero.ne n)
  · have hh : i ≤ j := le_of_not_gt hji
    simp only [hh, ite_true, hji, ite_false, add_zero]
    congr 1
    unfold targets
    ring

theorem backward_depth_formula (d : Fin n → ℤ) (i : Fin n) :
    backwardDepth d i = ∑ j : Fin n,
      ((targets d j-targets d i)/(n : ℤ) + if j < i then 1 else 0).toNat := by
  simp only [backwardDepth, crossing_quotient]

theorem backward_depth_head (d : Fin n → ℤ) :
    backwardDepth d 0 = ∑ j : Fin n, ((targets d j-targets d 0)/(n : ℤ)).toNat := by
  simp [backward_depth_formula]

theorem rotate_backward_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (i : Fin n) :
    backwardDepth (rotate d) i = backwardDepth d (finRotate n i) := by
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hc (j : Fin n) := LRX.RotationWords.crossing_recentered d 1 i j
  have he : LRX.RotationWords.localDisplacement d 1 = rotate d := by
    funext j
    simp only [LRX.RotationWords.localDisplacement, hv1, pow_one, LRX.L, rotate]
  rw [he] at hc
  simp only [hv1, pow_one, LRX.L] at hc
  unfold backwardDepth
  simp_rw [hc]
  exact Equiv.sum_comp (finRotate n)
    (fun j => (-LRX.AffineLift.crossing d (finRotate n i) j).toNat)

/-- The head has an inverted predecessor exactly when an earlier-period target exceeds it. -/
theorem backward_depth_head_pos_iff (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) :
    0 < backwardDepth d 0 ↔ ∃ j : Fin n, targets d 0 + n < targets d j := by
  rw [backward_depth_head, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_univ, true_and]
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hne (j : Fin n) : targets d j-targets d 0 ≠ n := by
    intro h
    have he : labels d j=labels d 0 := by
      have hc := congrArg (fun z : ℤ => (z : Fin n)) h
      have hcast (i : Fin n) : ((targets d i : ℤ) : Fin n)=labels d i := by simp [targets, labels]
      simp only [Int.cast_sub, hcast] at hc
      have hn0 : ((n : ℤ) : Fin n)=0 := by simp
      rw [hn0] at hc
      exact sub_eq_zero.mp hc
    have hj := hi he
    subst j
    simp at h
    omega
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j, ?_⟩
    have hq : 0 < (targets d j-targets d 0)/(n : ℤ) := by omega
    have hdiv := Int.ediv_mul_add_emod (targets d j-targets d 0) (n : ℤ)
    have hr := Int.emod_nonneg (targets d j-targets d 0) (ne_of_gt hn)
    have hh := hne j
    have hq1 : 1 ≤ (targets d j-targets d 0)/(n : ℤ) := by omega
    have hp := mul_le_mul_of_nonneg_right hq1 (le_of_lt hn)
    simp only [one_mul] at hp
    omega
  · rintro ⟨j,hj⟩
    refine ⟨j, ?_⟩
    have hdiv := Int.ediv_mul_add_emod (targets d j-targets d 0) (n : ℤ)
    have hr := Int.emod_lt_of_pos (targets d j-targets d 0) hn
    have hq : 0 < (targets d j-targets d 0)/(n : ℤ) := by nlinarith
    omega

/-- One backwards move consumes exactly one inverted predecessor. -/
theorem exchange_backward_depth (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1+1 < d 0) : backwardDepth (exchange d) 0 + 1 = backwardDepth d 1 := by
  have hv1 : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hnz : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hg : 0 < targets d 0-targets d 1 := by
    simp only [targets, Fin.val_zero, Nat.cast_zero, hv1, Nat.cast_one, zero_add]
    omega
  have hq : 0 ≤ (targets d 0-targets d 1)/(n : ℤ) := Int.ediv_nonneg (by omega) (by omega)
  have he : backwardDepth (exchange d) 0 =
      ∑ j : Fin n, ((targets d j-targets d 1)/(n : ℤ)).toNat := by
    rw [backward_depth_head]
    simp only [exchange_targets hn, Equiv.swap_apply_left]
    exact Equiv.sum_comp (Equiv.swap (0 : Fin n) 1)
      (fun j => ((targets d j-targets d 1)/(n : ℤ)).toNat)
  have hpoint (j : Fin n) :
      ((targets d j-targets d 1)/(n : ℤ) + if j < 1 then 1 else 0).toNat =
        ((targets d j-targets d 1)/(n : ℤ)).toNat + if j=0 then 1 else 0 := by
    by_cases hj : j=0
    · subst j
      have hjlt : (0 : Fin n) < 1 := by change 0 < (1 : Fin n).val; omega
      simp only [hjlt, ite_true]
      omega
    · have hjn : ¬ j < 1 := by
        have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        change ¬ j.val < (1 : Fin n).val
        omega
      simp only [hjn, hj, ite_false, add_zero]
  rw [he, backward_depth_formula]
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib]

/-- Comparing the first two entries preserves every other token's predecessor count. -/
theorem exchange_other_depth (hn : 2 ≤ n) (d : Fin n → ℤ) (i : Fin n)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : backwardDepth (exchange d) i = backwardDepth d i := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap 0 1
  have hv1 : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hi2 : 2 ≤ i.val := by
    have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (h.trans hv1.symm))
    omega
  have horder (j : Fin n) : τ j < i ↔ j < i := by
    by_cases hj0 : j=0
    · subst j
      simp only [τ, Equiv.swap_apply_left, Fin.lt_def, hv1, Fin.val_zero]
      omega
    · by_cases hj1 : j=1
      · subst j
        simp only [τ, Equiv.swap_apply_right, Fin.lt_def, hv1, Fin.val_zero]
        omega
      · simp only [τ, Equiv.swap_apply_of_ne_of_ne hj0 hj1]
  rw [backward_depth_formula, backward_depth_formula]
  simp only [exchange_targets hn, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  rw [← Equiv.sum_comp τ (fun j =>
    ((targets d (τ j)-targets d i)/(n : ℤ) + if j < i then 1 else 0).toNat)]
  simp only [τ, Equiv.swap_apply_self] at horder ⊢
  apply Finset.sum_congr rfl
  intro j _
  simp only [horder]

#print axioms crossing_quotient
#print axioms rotate_backward_depth
#print axioms backward_depth_head_pos_iff
#print axioms exchange_backward_depth
#print axioms exchange_other_depth
end LX.AffineScan
