import LRX.RecenteredCrossings
import LX.GreedyScan
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def targets (d : Fin n → ℤ) (i : Fin n) : ℤ := (i : ℤ) + d i

def inversions (d : Fin n → ℤ) : ℕ := LRX.LiftedModel.inversionCount (targets d)

private theorem swap_inversion_balance (hn : 2 ≤ n) (F : Fin n → ℤ) :
    LRX.LiftedModel.inversionCount (fun i => F (Equiv.swap 0 1 i)) +
        ((F 1 - F 0)/(n : ℤ)).natAbs =
      LRX.LiftedModel.inversionCount F + ((F 0 - F 1)/(n : ℤ)).natAbs := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap 0 1
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have hv1 : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hlt01 : (0 : Fin n) < 1 := by change 0 < (1 : Fin n).val; omega
  have hpoint (i j : Fin n) :
      (if τ i < τ j then ((F j-F i)/(n : ℤ)).natAbs else 0) +
        (if i=0 ∧ j=1 then ((F 1-F 0)/(n : ℤ)).natAbs else 0) =
      (if i < j then ((F j-F i)/(n : ℤ)).natAbs else 0) +
        (if i=1 ∧ j=0 then ((F 0-F 1)/(n : ℤ)).natAbs else 0) := by
    by_cases h01p : i=0 ∧ j=1
    · obtain ⟨rfl,rfl⟩ := h01p
      simp [τ, h01, hlt01, not_lt_of_ge (le_of_lt hlt01)]
    by_cases h10p : i=1 ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h10p
      simp [τ, h01, hlt01, not_lt_of_ge (le_of_lt hlt01)]
    have horder : τ i < τ j ↔ i < j := by
      by_cases hi0 : i=0 <;> by_cases hi1 : i=1 <;>
        by_cases hj0 : j=0 <;> by_cases hj1 : j=1
      all_goals simp only [τ, Equiv.swap_apply_def, hi0, hi1, hj0, hj1, ite_true, ite_false]
      all_goals try subst i
      all_goals try subst j
      all_goals simp_all only [Fin.lt_def, Fin.val_zero, hv1, Fin.ext_iff, ite_true, ite_false,
        h01, Ne.symm h01, not_false_eq_true]
      all_goals try omega
      all_goals simp_all
    simp only [horder, h01p, h10p, ite_false, add_zero]
  have hreindex : LRX.LiftedModel.inversionCount (fun i => F (τ i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        if τ i < τ j then ((F j-F i)/(n : ℤ)).natAbs else 0 := by
    unfold LRX.LiftedModel.inversionCount
    rw [← Equiv.sum_comp τ (fun i => ∑ j : Fin n,
      if i < j then ((F (τ j)-F (τ i))/(n : ℤ)).natAbs else 0)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp τ (fun j =>
      if τ i < j then ((F (τ j)-F (τ (τ i)))/(n : ℤ)).natAbs else 0)]
    simp only [τ, Equiv.swap_apply_self]
  have hsum := congrArg (fun g : Fin n → Fin n → ℕ => ∑ i, ∑ j, g i j)
    (funext fun i => funext (hpoint i))
  simp only [Finset.sum_add_distrib] at hsum
  have hs01 : (∑ i : Fin n, ∑ j : Fin n,
      if i=0 ∧ j=1 then ((F 1-F 0)/(n : ℤ)).natAbs else 0) =
      ((F 1-F 0)/(n : ℤ)).natAbs := by simp [ite_and]
  have hs10 : (∑ i : Fin n, ∑ j : Fin n,
      if i=1 ∧ j=0 then ((F 0-F 1)/(n : ℤ)).natAbs else 0) =
      ((F 0-F 1)/(n : ℤ)).natAbs := by simp [ite_and]
  rw [hs01, hs10] at hsum
  rw [hreindex]
  exact hsum

private theorem negative_quotient_abs (g : ℤ) (hg : 0 < g) (hdiv : ¬ (n : ℤ) ∣ g) :
    ((-g)/(n : ℤ)).natAbs = (g/(n : ℤ)).natAbs + 1 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hr0 := Int.emod_nonneg g (ne_of_gt hn)
  have hrn := Int.emod_lt_of_pos g hn
  have hrne : g % (n : ℤ) ≠ 0 := by
    intro h
    exact hdiv (Int.dvd_of_emod_eq_zero h)
  have hrpos : 0 < g % (n : ℤ) := by omega
  have hdecomp := Int.ediv_mul_add_emod g (n : ℤ)
  have hquot : (-g)/(n : ℤ) = -(g/(n : ℤ))-1 := by
    apply LRX.PeriodicBuffer.quotient_eq_of_bounds hn <;> nlinarith
  have hq0 : 0 ≤ g/(n : ℤ) := Int.ediv_nonneg (le_of_lt hg) (le_of_lt hn)
  rw [hquot]
  have habs := Int.natCast_natAbs (-(g/(n : ℤ))-1)
  have habs' := Int.natCast_natAbs (g/(n : ℤ))
  rw [abs_of_nonpos (by omega)] at habs
  rw [abs_of_nonneg hq0] at habs'
  omega

theorem exchange_targets (hn : 2 ≤ n) (d : Fin n → ℤ) (i : Fin n) :
    targets (exchange d) i = targets d (Equiv.swap 0 1 i) := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have hv1 : ((1 : Fin n) : ℤ) = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hi0 : i=0
  · subst i
    simp only [targets, exchange, Equiv.swap_apply_left, h01, ite_true, ite_false,
      Fin.val_zero, Nat.cast_zero, hv1, sub_zero]
    ring
  · by_cases hi1 : i=1
    · subst i
      simp only [targets, exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false,
        Fin.val_zero, Nat.cast_zero, hv1, add_zero]
      ring
    · simp [targets, exchange, Equiv.swap_apply_of_ne_of_ne hi0 hi1, hi0, hi1]

theorem exchange_inversions (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (hdesc : d 1+1 < d 0) :
    inversions (exchange d) + 1 = inversions d := by
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  have hv1 : ((1 : Fin n) : ℤ) = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hg : 0 < targets d 0-targets d 1 := by simp only [targets, Fin.val_zero, Nat.cast_zero, zero_add, hv1]; omega
  have hdiv : ¬ (n : ℤ) ∣ targets d 0-targets d 1 := by
    intro h
    have hh := LRX.AffineLift.cast_eq_of_modEq (Int.modEq_iff_dvd.mpr h)
    have hcast (i : Fin n) : ((targets d i : ℤ) : Fin n) = labels d i := by
      simp [targets, labels]
    have hl : labels d 1 = labels d 0 := by
      simpa only [hcast] using hh
    exact h01 (hi hl).symm
  have hp := negative_quotient_abs (targets d 0-targets d 1) hg hdiv
  have hbal := swap_inversion_balance hn (targets d)
  have he : (fun i => targets d (Equiv.swap 0 1 i)) = targets (exchange d) :=
    funext (fun i => (exchange_targets hn d i).symm)
  rw [he] at hbal
  change inversions (exchange d) + _ = inversions d + _ at hbal
  have hneg : -(targets d 0-targets d 1) = targets d 1-targets d 0 := by ring
  rw [hneg] at hp
  omega

theorem rotate_inversions (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d)) :
    inversions (rotate d) = inversions d := by
  let p : State n := Equiv.ofBijective (labels d) ⟨hi, Finite.surjective_of_injective hi⟩
  have hp (i : Fin n) : p i = labels d i := rfl
  have hcast (i : Fin n) : ((targets d i : ℤ) : Fin n) = labels d i := by
    simp [targets, labels]
  have hd : LRX.AffineLift.IsLift p.symm 0 d := by
    refine ⟨hb, ?_⟩
    intro i
    change Int.ModEq (n : ℤ) (targets d i) ((p i : ℤ) + 0)
    have hm := LRX.AffineLift.modEq_residue (n := n) (targets d i)
    have hcast' : (Fin.intCast (targets d i) : Fin n) = labels d i := hcast i
    rw [hcast'] at hm
    simpa only [hp, add_zero] using hm
  have hv1 : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hh := LRX.RotationWords.inversion_count_recentered (p := p.symm) 0 1 hd
  simp only [LRX.RotationWords.localDisplacement, hv1, pow_one, LRX.L] at hh
  exact hh

theorem inversions_zero (d : Fin n → ℤ) (hz : ∀ i, d i = 0) : inversions d = 0 := by
  unfold inversions LRX.LiftedModel.inversionCount
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have he : ((j : ℤ)-(i : ℤ))/(n : ℤ) = 0 := by
      apply LRX.PeriodicBuffer.quotient_eq_of_bounds hn <;> omega
    simp only [targets, hz, add_zero, he, Int.natAbs_zero]
  · rfl

/-- Exchanges in the actual forward scan are exactly the affine inversion price. -/
theorem ScanTrace.exchange_count (hn : 2 ≤ n) {d : Fin n → ℤ} {w : List Letter}
    (ht : ScanTrace d w) (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d)) :
    w.count .x = inversions d := by
  revert hb hi
  induction ht with
  | done hz =>
    intro _ _
    simpa only [List.count_nil] using (inversions_zero _ hz).symm
  | @left d w _ _ ht ih =>
    intro hb hi
    have hb' : ∑ i, rotate d i = 0 := (rotate_sum d).trans hb
    have hh := ih hb' (rotate_injective d hi)
    simpa [rotate_inversions hn d hb hi] using hh
  | @swap d w hdesc ht ih =>
    intro hb hi
    have hb' : ∑ i, exchange d i = 0 := (exchange_sum d).trans hb
    have hh := ih hb' (exchange_injective hn d hi)
    have hc := exchange_inversions hn d hi hdesc
    simp only [List.count_cons_self]
    omega

def paidWord (c : Fin n) (w : List Letter) : List Letter :=
  w ++ List.replicate (c - (w.count .l : Fin n)).val .l

def paidRotations (c : Fin n) (w : List Letter) : ℕ :=
  w.count .l + (c - (w.count .l : Fin n)).val

theorem length_eq_counts (w : List Letter) : w.length = w.count .l + w.count .x := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact cost of the actual LX word: inversions plus all rotations, including orientation. -/
theorem ScanTrace.paid_length (hn : 2 ≤ n) {d : Fin n → ℤ} {w : List Letter}
    (ht : ScanTrace d w) (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d))
    (c : Fin n) : (paidWord c w).length = inversions d + paidRotations c w := by
  simp only [paidWord, List.length_append, List.length_replicate, length_eq_counts,
    ht.exchange_count hn hb hi, paidRotations]
  omega

#print axioms exchange_inversions
#print axioms rotate_inversions
#print axioms ScanTrace.exchange_count
#print axioms ScanTrace.paid_length
end LX.AffineScan
