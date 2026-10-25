import LX.BackwardDepth
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem recentered_backward_depth (d : Fin n → ℤ) (r i : Fin n) :
    backwardDepth (LRX.RotationWords.localDisplacement d r) i =
      backwardDepth d ((LRX.L n ^ r.val) i) := by
  unfold backwardDepth
  simp_rw [LRX.RotationWords.crossing_recentered]
  exact Equiv.sum_comp (LRX.L n ^ r.val)
    (fun j => (-LRX.AffineLift.crossing d ((LRX.L n ^ r.val) i) j).toNat)

/-- Along an inversion, the smaller target has strictly more inverted predecessors. -/
theorem backward_depth_gt_head (d : Fin n → ℤ) (j : Fin n)
    (hj : targets d j < targets d 0) : backwardDepth d 0 < backwardDepth d j := by
  rw [backward_depth_head, backward_depth_formula]
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  apply Finset.sum_lt_sum
  · intro k _
    have hq : (targets d k-targets d 0)/(n : ℤ) ≤
        (targets d k-targets d j)/(n : ℤ) :=
      Int.ediv_le_ediv (by omega) (by omega)
    split_ifs <;> omega
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have hj0 : j ≠ 0 := by intro h; subst j; omega
    have hjpos : (0 : Fin n) < j := Fin.pos_iff_ne_zero.mpr hj0
    have hq : 0 ≤ (targets d 0-targets d j)/(n : ℤ) := Int.ediv_nonneg (by omega) (by omega)
    simp only [sub_self, Int.zero_ediv, Int.toNat_zero, hjpos, ite_true]
    omega

/-- A token with maximal backward depth has no outgoing inversion. -/
theorem maximum_depth_nonpositive_crossings (d : Fin n → ℤ) (a : Fin n)
    (ha : ∀ i, backwardDepth d i ≤ backwardDepth d a) :
    ∀ j, LRX.AffineLift.crossing d a j ≤ 0 := by
  intro j
  by_contra h
  let r := LRX.L n ^ a.val
  let b : Fin n := r.symm j
  let e := LRX.RotationWords.localDisplacement d a
  have hr0 : r 0 = a := by simp [r, LRX.AffineLift.rotation_power_apply]
  have hrb : r b = j := r.apply_symm_apply j
  have hc : LRX.AffineLift.crossing e 0 b = LRX.AffineLift.crossing d a j := by
    have hh := LRX.RotationWords.crossing_recentered d a 0 b
    change LRX.AffineLift.crossing e 0 b = LRX.AffineLift.crossing d (r 0) (r b) at hh
    simpa only [hr0, hrb] using hh
  have htarget : targets e b < targets e 0 := by
    have hh : 0 < LRX.AffineLift.crossing e 0 b := by omega
    have hnum : LRX.AffineLift.crossingNumerator e 0 b = targets e b-targets e 0 := by
      simp [LRX.AffineLift.crossingNumerator, targets]
    simp only [LRX.AffineLift.crossing, hnum] at hh
    by_contra hnot
    have hq := Int.ediv_nonneg (by omega : 0 ≤ targets e b-targets e 0)
      (show (0 : ℤ) ≤ n by positivity)
    omega
  have hlt := backward_depth_gt_head e b htarget
  have h0 := recentered_backward_depth d a 0
  have hb := recentered_backward_depth d a b
  change backwardDepth e 0 = backwardDepth d (r 0) at h0
  change backwardDepth e b = backwardDepth d (r b) at hb
  rw [hr0] at h0
  rw [hrb] at hb
  rw [h0, hb] at hlt
  have := ha j
  omega

/-- The largest backward depth is attained at a token whose displacement is its negative. -/
theorem exists_depth_extreme {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) :
    ∃ a : Fin n, (∀ i, backwardDepth d i ≤ backwardDepth d a) ∧
      (backwardDepth d a : ℤ) = -d a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
    ⟨0, Finset.mem_univ _⟩ (backwardDepth d)
  have hmax (i : Fin n) : backwardDepth d i ≤ backwardDepth d a := by
    rw [← ha]
    exact Finset.le_sup (f := backwardDepth d) (Finset.mem_univ i)
  refine ⟨a, hmax, ?_⟩
  have hc := maximum_depth_nonpositive_crossings d a hmax
  have hrow := LRX.AffineLift.crossing_row_sum hd a
  have he (j : Fin n) : ((-LRX.AffineLift.crossing d a j).toNat : ℤ) =
      -LRX.AffineLift.crossing d a j := Int.toNat_of_nonneg (by have := hc j; omega)
  simp only [backwardDepth, Nat.cast_sum, he, Finset.sum_neg_distrib, hrow]

/-- A lower displacement bound controls every token's backward exchanges. -/
theorem backward_depth_le_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (h : ℤ) (hlo : ∀ i, -h ≤ d i) (i : Fin n) :
    (backwardDepth d i : ℤ) ≤ h := by
  obtain ⟨a,hmax,he⟩ := exists_depth_extreme hd
  have hh : (backwardDepth d i : ℤ) ≤ backwardDepth d a := by exact_mod_cast hmax i
  have := hlo a
  omega

#print axioms backward_depth_gt_head
#print axioms exists_depth_extreme
#print axioms backward_depth_le_strip
end LX.AffineScan
